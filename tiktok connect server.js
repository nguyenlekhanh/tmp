/**
 * CHRISTIAN PRAYER LIVE
 * Faith • Hope • Love — "Pray Together. Grow in Faith."
 *
 * Bun.js HTTP + WebSocket JSON-RPC 2.0 server, preserving the original
 * TikTok Live RPC architecture (same endpoints, same event pipeline) while
 * serving a general Christian prayer livestream for the United States market.
 *
 * Engines:
 *  - TikTok Live Connector (comments, likes, follows, shares, gifts)
 *  - Piper multilingual TTS (American English + Vietnamese)
 *  - Local licensed background imagery with scheduled rotation
 */
const express = require('express');
const http = require('http');
const path = require('path');
const fs = require('fs');
const { spawn } = require('child_process');
const cors = require('cors');
const { WebSocketServer } = require('ws');
const { TikTokLiveConnection, WebcastEvent, ControlEvent } = require('tiktok-live-connector');

const { loadConfig, loadMessages } = require('./config/config');
const { MessageLibrary } = require('./lib/messages');
const { discoverVoices, resolveVoice, defaultVoiceId } = require('./lib/voices');
const { ShowProgram, PRAYER_THEMES } = require('./lib/show');
const { QuizEngine, QUESTIONS: QUIZ_QUESTIONS } = require('./lib/quiz');
const { MusicLibrary } = require('./lib/music-library');
const { Congregation } = require('./lib/congregation');
const { CopyrightAudit } = require('./lib/copyright-audit');
const { BroadcastSafety } = require('./lib/broadcast-safety');
const { SmartSchedule } = require('./lib/schedule');
const { HealthMonitor, wavStats } = require('./lib/health');
const { MusicIntegrity } = require('./lib/music-integrity');
const { ImageLibrary, isIgnoredImageName, imageDimensions } = require('./lib/image-library');

const CONFIG = loadConfig();
const PORT = CONFIG.port || 3000;
const DATA_DIR = path.join(__dirname, 'data');
const TTS_CACHE_DIR = path.join(DATA_DIR, 'tts-cache');
const STATE_FILE = path.join(DATA_DIR, 'prayer-state.json');
const HEALTH_STATE_FILE = path.join(DATA_DIR, 'health-state.json');
const SCHEDULE_FILE = path.join(__dirname, 'config', 'schedule.json');
const LEGACY_STATE_FILE = path.join(DATA_DIR, 'merit-state.json');
const PUBLIC_DIR = path.join(__dirname, 'public');
const CHRISTIAN_ASSETS_DIR = path.join(PUBLIC_DIR, 'assets', 'christian');
const ASSET_MANIFEST_FILE = path.join(CHRISTIAN_ASSETS_DIR, 'asset-manifest.json');
const copyrightAudit = new CopyrightAudit({ root: __dirname });
const broadcastSafety = new BroadcastSafety({ root: __dirname });
const imageLibrary = new ImageLibrary({
  root: __dirname,
  assetsDir: CHRISTIAN_ASSETS_DIR,
  manifestPath: ASSET_MANIFEST_FILE,
  statePath: path.join(DATA_DIR, 'image-library-state.json')
});
let broadcastSafeMode = true;

fs.mkdirSync(TTS_CACHE_DIR, { recursive: true });

const messageLibrary = new MessageLibrary();
const VOICES = discoverVoices();

// ============================================================================
// 1. BRAND & IMMUTABLE CONFIG EXPOSED TO CLIENTS
// ============================================================================
const BRAND = {
  name: 'CHRISTIAN PRAYER LIVE',
  tagline: 'FAITH • HOPE • LOVE',
  secondaryTagline: 'Pray Together. Grow in Faith.',
  market: 'United States',
  tradition: 'General Christian'
};

// ============================================================================
// 2. PIPER TTS WORKER MANAGER (LANGUAGE AWARE: EN-US + VI-VN)
// ============================================================================
let ttsManager = null;
const {
  mergeEngagementSettings,
  EngagementMessages,
  EngagementScheduler,
  ENGAGEMENT_DEFAULTS
} = require('./lib/engagement');

let showProgram = null;
let engagementScheduler = null;
let engagementMessages = null;
let quizEngine = null;
let healthMonitor = null;
let smartSchedule = null;
let tiktokWatchdog = null;
// Set while a show narration is playing so two prayers never talk over each other.
let narrationBusyUntil = 0;
// Last cue of any kind (welcome included), replayed to a stage that reconnects.
let lastPublishedCue = null;
let lastPublishedAt = 0;
// Farewell screen lock: a second click must never stack two readings.
let farewellUntil = 0;
let farewellCue = null;
let farewellEndTimer = null;

class PiperManager {
  constructor() {
    this.proc = null;
    this.ready = false;
    this.status = 'starting';
    this.voices = VOICES;
    this.defaults = {
      en: defaultVoiceId(VOICES, CONFIG, 'en'),
      vi: defaultVoiceId(VOICES, CONFIG, 'vi')
    };
    this.pending = new Map();
    this.inflight = new Map();
    this.reqCounter = 0;
    this.buffer = '';
    this.error = null;
    this.loadSec = null;
    // Auto recovery: delays double up to one minute, with a hard rate limit so a
    // permanently broken voice install cannot spin forever.
    this.recovery = {
      attempts: 0,
      history: [],
      timer: null,
      nextAt: null,
      suspended: false,
      lastExit: null,
      lastExitAt: null,
      lastReadyAt: null,
      starting: false
    };
    this.readyTimer = null;
    this.requestedStop = false;
    this.onIncident = null;
    this.startWorker({ reason: 'startup' });
  }

  /** Records a recovery event without coupling the manager to the health module. */
  reportIncident(incident) {
    if (typeof this.onIncident === 'function') {
      try {
        this.onIncident(incident);
      } catch (err) {
        console.warn('[Piper] Incident handler failed:', err.message);
      }
    }
  }

  resolvePythonBin() {
    const candidates = [
      path.join(__dirname, '.venv', 'Scripts', 'python.exe'),
      path.join(__dirname, '.venv', 'bin', 'python'),
      'python',
      'python3'
    ];
    for (const candidate of candidates) {
      if (candidate.includes(path.sep) || candidate.includes('/')) {
        if (fs.existsSync(candidate)) return candidate;
      } else {
        return candidate;
      }
    }
    return 'python';
  }

  startWorker({ reason = 'manual' } = {}) {
    if (this.recovery.timer) {
      clearTimeout(this.recovery.timer);
      this.recovery.timer = null;
    }
    this.recovery.nextAt = null;
    this.recovery.starting = true;
    // A manual retry must replace the worker, never leave a second one speaking.
    if (this.proc) {
      const previous = this.proc;
      this.proc = null;
      try {
        previous.removeAllListeners();
      } catch (_) {}
      try {
        previous.kill();
      } catch (_) {}
    }
    const pyBin = this.resolvePythonBin();
    const scriptPath = path.join(__dirname, 'tts_worker.py');
    console.log(`[Piper] Starting TTS worker: ${pyBin}${reason !== 'startup' ? ` (${reason})` : ''}`);
    this.status = 'loading';
    this.error = null;

    let child;
    try {
      child = spawn(pyBin, [scriptPath], {
        cwd: __dirname,
        stdio: ['pipe', 'pipe', 'pipe'],
        env: { ...process.env, PYTHONIOENCODING: 'utf-8' }
      });
    } catch (err) {
      this.recovery.starting = false;
      this.status = 'error';
      this.error = err.message;
      console.error('[Piper] Could not spawn worker:', err.message);
      this.scheduleRestart(`spawn failed: ${err.message}`);
      return;
    }
    this.proc = child;

    // A voice that never becomes ready must not hang narration forever.
    clearTimeout(this.readyTimer);
    this.readyTimer = setTimeout(() => {
      if (this.proc !== child || this.ready) return;
      console.warn('[Piper] Worker did not become ready within 90s — restarting it.');
      try {
        child.kill();
      } catch (_) {}
    }, 90000);
    if (typeof this.readyTimer.unref === 'function') this.readyTimer.unref();

    child.stdout.on('data', (chunk) => {
      if (this.proc !== child) return;
      this.buffer += chunk.toString('utf8');
      const lines = this.buffer.split('\n');
      this.buffer = lines.pop() || '';
      for (const line of lines) {
        if (!line.trim()) continue;
        this.handleWorkerLine(line.trim());
      }
    });

    child.stderr.on('data', (chunk) => {
      const msg = chunk.toString('utf8').trim();
      if (msg) console.log(`[Piper] ${msg}`);
    });

    child.on('error', (err) => {
      if (this.proc !== child) return;
      this.proc = null;
      this.recovery.starting = false;
      this.ready = false;
      this.status = 'error';
      this.error = `Piper worker failed: ${err.message}. Install it with: uv venv .venv && uv pip install piper-tts`;
      console.error(`[Piper] ${this.error}`);
      broadcastNotification('tts.status', this.getStatus());
      this.scheduleRestart(this.error);
    });

    child.on('exit', (code, signal) => {
      if (this.proc !== child) return;
      this.proc = null;
      this.recovery.starting = false;
      clearTimeout(this.readyTimer);
      this.ready = false;
      this.status = this.requestedStop ? 'stopped' : 'restarting';
      const description = `Piper worker exited (code ${code}${signal ? `, ${signal}` : ''})`;
      this.recovery.lastExit = description;
      this.recovery.lastExitAt = new Date().toISOString();
      if (!this.requestedStop) {
        this.error = description;
        console.warn(`[Piper] ${description}`);
      }
      // Reject in-flight synthesis once: pending speech is never replayed twice.
      for (const [, item] of this.pending) {
        clearTimeout(item.timer);
        item.resolve({ ok: false, error: 'Piper worker restarted; the request was not repeated.' });
      }
      this.pending.clear();
      broadcastNotification('tts.status', this.getStatus());
      if (!this.requestedStop) this.scheduleRestart(description);
    });
  }

  /** Exponential backoff with a one-hour rate limit and an admin-visible stop. */
  scheduleRestart(reason) {
    if (this.requestedStop || this.recovery.suspended) return;
    const now = Date.now();
    this.recovery.history = this.recovery.history.filter((at) => now - at < 60 * 60 * 1000);
    if (this.recovery.history.length >= 8) {
      this.recovery.suspended = true;
      this.status = 'error';
      this.error = 'Piper restarted 8 times in an hour. Automatic retries paused — use Retry Piper in the dashboard.';
      console.error(`[Piper] ${this.error}`);
      this.reportIncident({
        component: 'piper',
        severity: 'error',
        message: this.error,
        action: 'Automatic restarts paused',
        result: 'Livestream continues without narration',
        recoveryFailed: true
      });
      broadcastNotification('tts.status', this.getStatus());
      return;
    }
    const delays = [2000, 5000, 10000, 30000, 60000];
    const delay = delays[Math.min(this.recovery.attempts, delays.length - 1)];
    this.recovery.attempts += 1;
    this.recovery.history.push(now);
    this.recovery.nextAt = now + delay;
    this.status = 'restarting';
    clearTimeout(this.recovery.timer);
    this.recovery.timer = setTimeout(() => {
      this.recovery.timer = null;
      this.startWorker({ reason: `auto-recovery after ${Math.round(delay / 1000)}s backoff` });
    }, delay);
    if (typeof this.recovery.timer.unref === 'function') this.recovery.timer.unref();
    console.warn(`[Piper] Auto-recovery in ${delay / 1000}s (${reason})`);
    this.reportIncident({
      component: 'piper',
      severity: 'warning',
      message: reason,
      action: `Automatic restart in ${delay / 1000}s (attempt ${this.recovery.attempts})`,
      result: 'Queued'
    });
    broadcastNotification('tts.status', this.getStatus());
  }

  /** Manual recovery button: resets the rate limit, then restarts once. */
  recover({ manual = true } = {}) {
    if (manual) {
      this.recovery.history = [];
      this.recovery.suspended = false;
      this.recovery.attempts = 0;
    }
    if (this.recovery.timer) {
      clearTimeout(this.recovery.timer);
      this.recovery.timer = null;
    }
    this.requestedStop = false;
    this.startWorker({ reason: manual ? 'manual retry' : 'recovery' });
    this.reportIncident({
      component: 'piper',
      severity: 'info',
      message: 'Piper restart requested.',
      action: manual ? 'Manual restart from the dashboard' : 'Automatic restart',
      result: 'Worker starting',
      recovery: true
    });
    return this.getHealth();
  }

  getHealth() {
    const now = Date.now();
    const lastHour = this.recovery.history.filter((at) => now - at < 60 * 60 * 1000).length;
    return {
      status: this.status,
      ready: this.ready,
      suspended: this.recovery.suspended,
      restartAttempts: this.recovery.attempts,
      restartsLastHour: lastHour,
      nextRestartAt: this.recovery.nextAt ? new Date(this.recovery.nextAt).toISOString() : null,
      lastExit: this.recovery.lastExit,
      lastExitAt: this.recovery.lastExitAt,
      lastReadyAt: this.recovery.lastReadyAt,
      pending: this.pending.size,
      error: this.error
    };
  }

  shutdown() {
    this.requestedStop = true;
    clearTimeout(this.recovery.timer);
    this.recovery.timer = null;
    clearTimeout(this.readyTimer);
    try {
      if (this.proc) this.proc.kill();
    } catch (_) {}
  }

  handleWorkerLine(line) {
    let msg;
    try {
      msg = JSON.parse(line);
    } catch (_) {
      console.log('[Piper stdout]', line);
      return;
    }
    if (msg.type === 'status') {
      this.status = msg.status || 'loading';
      broadcastNotification('tts.status', this.getStatus());
    } else if (msg.type === 'ready') {
      const recovered = this.recovery.attempts > 0;
      this.ready = true;
      this.status = 'ready';
      this.error = msg.loadError || null;
      this.loadSec = msg.loadSec;
      this.recovery.starting = false;
      this.recovery.suspended = false;
      this.recovery.attempts = 0;
      this.recovery.lastReadyAt = new Date().toISOString();
      clearTimeout(this.readyTimer);
      if (recovered) {
        this.reportIncident({
          component: 'piper',
          severity: 'info',
          message: 'Piper worker recovered and is speaking again.',
          action: 'Automatic restart',
          result: 'Ready',
          recovery: true
        });
      }
      if (Array.isArray(msg.voices) && msg.voices.length > 0) {
        this.voices = msg.voices;
      }
      if (msg.defaults) this.defaults = { ...this.defaults, ...msg.defaults };
      const labels = this.voices.map((v) => `${v.language}:${v.id}`).join(', ');
      console.log(`[Piper] Ready in ${msg.loadSec}s — voices: ${labels}`);
      broadcastNotification('tts.status', this.getStatus());
    } else if (msg.type === 'result' && msg.id != null) {
      const entry = this.pending.get(msg.id);
      if (entry) {
        clearTimeout(entry.timer);
        this.pending.delete(msg.id);
        entry.resolve(msg);
      }
    } else if (msg.type === 'error') {
      this.error = msg.error || 'Unknown Piper error';
      if (msg.fatal) this.status = 'error';
      console.error('[Piper]', this.error);
      broadcastNotification('tts.status', this.getStatus());
    }
  }

  resolveVoiceFor(language, requested) {
    const voice = resolveVoice(this.voices, language, requested);
    return voice ? voice.id : null;
  }

  getStatus() {
    return {
      ready: this.ready,
      status: this.status,
      engine: 'Piper (local ONNX)',
      language: state.settings.ttsLanguage || CONFIG.language.default,
      voices: this.voices,
      enVoice: state.settings.enVoice,
      vnVoice: state.settings.vnVoice,
      languageVoices: {
        en: this.voices.filter((v) => v.language === 'en'),
        vi: this.voices.filter((v) => v.language === 'vi')
      },
      enabled: Boolean(state.settings.ttsEnabled),
      volume: state.settings.ttsVolume,
      rate: state.settings.ttsRate,
      loadSec: this.loadSec,
      error: this.error,
      health: this.getHealth()
    };
  }

  synthesize(text, options = {}) {
    const cleanText = String(text || '').trim();
    if (!cleanText) return Promise.resolve({ ok: false, error: 'Empty text' });
    const language = options.lang === 'vi' ? 'vi' : options.lang === 'en' ? 'en' : detectLanguage(cleanText);
    const configuredVoice = language === 'vi' ? state.settings.vnVoice : state.settings.enVoice;
    const voice = this.resolveVoiceFor(language, options.voice || configuredVoice);
    if (!voice) {
      return Promise.resolve({ ok: false, error: `No ${language} Piper voice is installed` });
    }
    const rate = clampNumber(options.rate ?? state.settings.ttsRate, 0.6, 1.6, 1.0);
    const dedupKey = `${voice}::${rate.toFixed(2)}::${cleanText}`;
    if (this.inflight.has(dedupKey)) return this.inflight.get(dedupKey);

    const promise = new Promise((resolve) => {
      if (!this.proc || !this.ready) {
        return resolve({
          ok: false,
          error: this.status === 'error'
            ? this.error || 'Piper is not available'
            : `Piper is ${this.status}. Please wait a moment and try again.`
        });
      }
      const id = ++this.reqCounter;
      const timer = setTimeout(() => {
        this.pending.delete(id);
        resolve({ ok: false, error: 'Piper synthesis timed out' });
      }, 60000);
      this.pending.set(id, { resolve, timer });
      const payload = JSON.stringify({ id, text: cleanText, lang: language, voice, rate }) + '\n';
      try {
        this.proc.stdin.write(payload);
      } catch (err) {
        clearTimeout(timer);
        this.pending.delete(id);
        resolve({ ok: false, error: `Piper write failed: ${err.message}` });
      }
    }).finally(() => this.inflight.delete(dedupKey));

    this.inflight.set(dedupKey, promise);
    return promise;
  }
}

// ============================================================================
// 3. BACKGROUND IMAGE DISCOVERY (locally served licensed assets only)
// ============================================================================
function loadAssetManifest() {
  try {
    if (!fs.existsSync(ASSET_MANIFEST_FILE)) return new Map();
    const entries = JSON.parse(fs.readFileSync(ASSET_MANIFEST_FILE, 'utf8'));
    const map = new Map();
    for (const entry of entries) {
      map.set(entry.file.replace(/\\/g, '/'), entry);
    }
    return map;
  } catch (err) {
    console.warn('[Assets] Could not read asset-manifest.json:', err.message);
    return new Map();
  }
}

function walkImages(dir, baseDir, results) {
  let entries = [];
  try {
    entries = fs.readdirSync(dir, { withFileTypes: true });
  } catch (_) {
    return;
  }
  for (const entry of entries) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      if (entry.name === 'overlays') continue;
      walkImages(full, baseDir, results);
    } else if (/\.(jpe?g|png|webp)$/i.test(entry.name) && !isIgnoredImageName(entry.name)) {
      // Ignore thumbnails, hidden files and anything the scanner would reject,
      // so the stage catalog and the image library stay in agreement.
      const dimensions = imageDimensions(full);
      if (!dimensions.width || !dimensions.height) continue;
      const relative = path.relative(baseDir, full).replace(/\\/g, '/');
      results.push({ full, relative });
    }
  }
}

function loadBackgroundImages() {
  const manifest = loadAssetManifest();
  const found = [];
  walkImages(CHRISTIAN_ASSETS_DIR, CHRISTIAN_ASSETS_DIR, found);
  const images = found.map(({ relative }) => {
    const meta = manifest.get(relative) || {};
    const folder = relative.includes('/') ? relative.split('/')[0] : 'backgrounds';
    const url = `/assets/christian/${relative}`;
    return {
      url,
      path: relative,
      copyright: broadcastSafety.image(url, { safeMode: broadcastSafeMode }),
      category: folder,
      title: String(meta.title || path.basename(relative, path.extname(relative)))
        .replace(/\.(jpe?g|png|webp)$/i, '')
        .replace(/[_]+/g, ' ')
        .replace(/\s+/g, ' ')
        .trim(),
      license: meta.license || 'See asset-manifest.json',
      attribution: meta.attribution || '',
      width: meta.width || null,
      height: meta.height || null
    };
  });
  images.sort((a, b) => a.path.localeCompare(b.path));
  const categories = [...new Set(images.map((img) => img.category))];
  return { images, categories };
}

const BACKGROUNDS = loadBackgroundImages();

// ============================================================================
// 3b. AMBIENT WORSHIP MUSIC CATALOG
// ============================================================================
const MUSIC_DIR = path.join(CHRISTIAN_ASSETS_DIR, 'audio');
const MUSIC_MANIFEST_FILE = path.join(MUSIC_DIR, 'music-manifest.json');

const MUSIC_INTEGRITY = new MusicIntegrity({
  dir: MUSIC_DIR,
  manifestPath: MUSIC_MANIFEST_FILE
});

const MUSIC_LIBRARY = new MusicLibrary({
  dir: MUSIC_DIR,
  manifestPath: MUSIC_MANIFEST_FILE,
  backupPath: path.join(MUSIC_DIR, 'music-manifest.backup.json'),
  removedDir: path.join(__dirname, 'docs', 'backups', 'music-removed'),
  publicUrl: '/assets/christian/audio'
});

// Mutated in place by applyMusicCatalog so every reference below stays current.
const MUSIC = {
  tracks: [],
  allTracks: [],
  byId: new Map(),
  libraryById: new Map(),
  manifest: {},
  categories: [],
  defaultVolume: 0.1,
  duckedVolume: 0.035,
  totalDurationSeconds: 0,
  libraryMeta: { total: 0, enabled: 0, disabled: 0, totalDurationSeconds: 0, categories: [] }
};

function applyMusicCatalog(catalog) {
  if (!catalog) return MUSIC;
  MUSIC.tracks = broadcastSafety.annotateMusic(catalog.tracks, broadcastSafeMode);
  MUSIC.allTracks = broadcastSafety.annotateMusic(catalog.allTracks, broadcastSafeMode);
  MUSIC.byId = new Map(MUSIC.tracks.map((track) => [track.id, track]));
  MUSIC.libraryById = new Map(MUSIC.allTracks.map((track) => [track.id, track]));
  MUSIC.manifest = catalog.manifest;
  MUSIC.categories = catalog.categories;
  MUSIC.defaultVolume = catalog.defaultVolume;
  MUSIC.duckedVolume = catalog.duckedVolume;
  MUSIC.totalDurationSeconds = catalog.totalDurationSeconds;
  MUSIC.libraryMeta = catalog.libraryMeta;
  return MUSIC;
}

function isMusicEligible(track) {
  if (!track) return false;
  return broadcastSafety.music(track.file || track.url, { safeMode: broadcastSafeMode }).eligible;
}

function playableMusicTracks() {
  return MUSIC.tracks.filter((track) => !broadcastSafeMode || isMusicEligible(track));
}

applyMusicCatalog(MUSIC_LIBRARY.readCatalog());

const BACKGROUND_LAYER_FILES = ['golden-light-rays.png', 'gold-bokeh-particles.png', 'soft-vignette.png']
  .map((file) => `/assets/christian/overlays/${file}`)
  .filter((url) => fs.existsSync(path.join(PUBLIC_DIR, url.replace('/assets/', 'assets/'))));

// Fixed stage overlays are broadcast assets too, but they are never part of rotation.
const OVERLAY_IMAGES = BACKGROUND_LAYER_FILES.map((url) => ({
  url,
  path: url.replace('/assets/christian/', ''),
  category: 'overlays',
  title: path.basename(url, path.extname(url)).replace(/_/g, ' ')
}));

// ============================================================================
// 4. STATE
// ============================================================================
function defaultSettings() {
  const eligibleBackgrounds = BACKGROUNDS.images.filter((img) => img.copyright?.eligible);
  const firstBackground = eligibleBackgrounds.find((img) => img.path.includes('cathedral-01'))
    || eligibleBackgrounds.find((img) => img.category === 'cathedral')
    || eligibleBackgrounds.find((img) => img.path.includes('church-02'))
    || eligibleBackgrounds[0]
    || null;
  const configuredTrack = MUSIC.byId.get(CONFIG.backgroundMusic.track);
  const defaultTrack = configuredTrack && isMusicEligible(configuredTrack)
    ? configuredTrack.id
    : (MUSIC.tracks.find(isMusicEligible)?.id || '');
  return {
    copyrightSafeMode: true,
    ttsEnabled: CONFIG.tts.enabled,
    ttsLanguage: CONFIG.language.default,
    enVoice: defaultVoiceId(VOICES, CONFIG, 'en'),
    vnVoice: defaultVoiceId(VOICES, CONFIG, 'vi'),
    ttsVolume: CONFIG.tts.volume,
    ttsRate: CONFIG.tts.rate,
    sfxEnabled: true,
    music: {
      enabled: CONFIG.backgroundMusic.enabled,
      volume: CONFIG.backgroundMusic.volume,
      duckVolume: CONFIG.backgroundMusic.duckVolume,
      track: defaultTrack,
      autoplay: CONFIG.backgroundMusic.autoplay,
      shuffle: CONFIG.backgroundMusic.shuffle,
      repeat: CONFIG.backgroundMusic.repeat,
      paused: false
    },
    show: {
      enabled: CONFIG.show.enabled,
      paused: CONFIG.show.paused,
      welcomeEnabled: CONFIG.show.welcomeEnabled,
      narration: CONFIG.show.narration,
      theme: CONFIG.show.theme,
      pace: CONFIG.show.pace
    },
    quiz: {
      enabled: CONFIG.quiz.enabled,
      frequencyMinutes: CONFIG.quiz.frequencyMinutes,
      revealSeconds: CONFIG.quiz.revealSeconds,
      tts: CONFIG.quiz.tts
    },
    gifts: {
      announce: CONFIG.gifts.announce,
      tts: CONFIG.gifts.tts
    },
    autoSim: false,
    autoSimIntervalMs: 12000,
    background: {
      enabled: CONFIG.background.rotation,
      intervalSeconds: CONFIG.background.intervalSeconds,
      category: CONFIG.background.category,
      randomize: CONFIG.background.randomize,
      transitionMs: CONFIG.background.transitionMs,
      sceneMatch: CONFIG.background.sceneMatch,
      current: firstBackground ? firstBackground.url : ''
    },
    prayer: {
      autoApprove: CONFIG.prayer.autoApprove,
      paused: CONFIG.prayer.paused,
      maxQueue: CONFIG.prayer.maxQueue,
      cooldownSeconds: CONFIG.prayer.cooldownSeconds,
      interactionEnabled: CONFIG.prayer.interactionEnabled
    },
    congregation: {
      enabled: true,
      showNames: true,
      inactivityMinutes: 20,
      maxVisible: 50
    },
    engagement: mergeEngagementSettings({}),
    tiktok: {
      autoReconnect: true,
      maxRetries: 6,
      retrySeconds: 10
    }
  };
}

const DEFAULT_STATE = {
  candlesLit: 12,
  prayerCount: 0,
  amenCount: 0,
  blessingsCount: 0,
  verseCount: 0,
  giftCount: 0,
  followCount: 0,
  shareCount: 0,
  likeCount: 0,
  totalMerit: 0,
  activeCandles: 6,
  community: {},
  prayerRequests: [],
  featuredVerse: messageLibrary.bibleVerse() || { text: 'The Lord is my shepherd; I shall not want.', reference: 'Psalm 23:1 (KJV)' },
  chatFeed: [],
  recentEvents: [],
  showHistory: [],
  quizRecent: [],
  settings: defaultSettings(),
  tiktok: {
    connected: false,
    connecting: false,
    reconnecting: false,
    username: CONFIG.tiktok.username || '',
    roomId: null,
    viewerCount: 0,
    lastError: null,
    lastDisconnectReason: null,
    lastConnectedAt: null,
    connectStartedAt: null,
    lastEventAt: null,
    reconnectAttempts: 0,
    nextRetryAt: null,
    requiresAttention: false
  }
};

function loadState() {
  try {
    if (fs.existsSync(STATE_FILE)) {
      const saved = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
      return {
        ...JSON.parse(JSON.stringify(DEFAULT_STATE)),
        ...saved,
        community: saved.community || {},
        prayerRequests: Array.isArray(saved.prayerRequests) ? saved.prayerRequests : [],
        featuredVerse: saved.featuredVerse || DEFAULT_STATE.featuredVerse,
        chatFeed: Array.isArray(saved.chatFeed) ? saved.chatFeed : [],
        recentEvents: Array.isArray(saved.recentEvents) ? saved.recentEvents : [],
        showHistory: Array.isArray(saved.showHistory) ? saved.showHistory : [],
        quizRecent: Array.isArray(saved.quizRecent) ? saved.quizRecent : [],
        settings: {
          ...DEFAULT_STATE.settings,
          ...(saved.settings || {}),
          background: { ...DEFAULT_STATE.settings.background, ...((saved.settings || {}).background || {}) },
          prayer: { ...DEFAULT_STATE.settings.prayer, ...((saved.settings || {}).prayer || {}) },
          music: { ...DEFAULT_STATE.settings.music, ...((saved.settings || {}).music || {}) },
          show: { ...DEFAULT_STATE.settings.show, ...((saved.settings || {}).show || {}) },
          engagement: mergeEngagementSettings(
            DEFAULT_STATE.settings.engagement,
            (saved.settings || {}).engagement || {}
          ),
          quiz: { ...DEFAULT_STATE.settings.quiz, ...((saved.settings || {}).quiz || {}) },
          gifts: { ...DEFAULT_STATE.settings.gifts, ...((saved.settings || {}).gifts || {}) },
          congregation: { ...DEFAULT_STATE.settings.congregation, ...((saved.settings || {}).congregation || {}) },
          tiktok: { ...DEFAULT_STATE.settings.tiktok, ...((saved.settings || {}).tiktok || {}) }
        },
        tiktok: { ...DEFAULT_STATE.tiktok }
      };
    }
  } catch (err) {
    console.warn(`[State] Could not read prayer-state.json (${err.message}); using defaults.`);
  }
  if (fs.existsSync(LEGACY_STATE_FILE)) {
    console.log('[State] Legacy merit-state.json found; starting a fresh Christian Prayer Live state (legacy file untouched).');
  }
  return JSON.parse(JSON.stringify(DEFAULT_STATE));
}

const state = loadState();
broadcastSafeMode = state.settings.copyrightSafeMode !== false;
applyMusicCatalog(MUSIC_LIBRARY.readCatalog());
BACKGROUNDS.images = broadcastSafety.annotateImages(BACKGROUNDS.images, broadcastSafeMode);

// Repair a saved background that is missing or blocked by Copyright Safe Mode.
const savedBackground = BACKGROUNDS.images.find((img) => img.url === state.settings.background.current);
const eligibleBackground = BACKGROUNDS.images.find((img) => img.copyright?.eligible);
if (broadcastSafeMode) {
  if (!savedBackground || !savedBackground.copyright?.eligible) {
    state.settings.background.current = eligibleBackground?.url || '';
  }
} else if (BACKGROUNDS.images.length > 0 && !savedBackground) {
  state.settings.background.current = BACKGROUNDS.images[0].url;
}
if (state.settings.background.category !== 'all' && !BACKGROUNDS.categories.includes(state.settings.background.category)) {
  state.settings.background.category = 'all';
}
// A category made entirely of blocked assets cannot drive an automatic rotation.
if (broadcastSafeMode && state.settings.background.category !== 'all') {
  const hasEligible = BACKGROUNDS.images.some(
    (img) => img.category === state.settings.background.category && img.copyright?.eligible
  );
  if (!hasEligible) state.settings.background.category = 'all';
}

// Repair a saved music track that is missing, disabled or blocked.
if (state.settings.music) {
  const savedTrack = MUSIC.byId.get(state.settings.music.track);
  if (!savedTrack) {
    const playable = playableMusicTracks();
    state.settings.music.track = playable[0]?.id || '';
    if (!state.settings.music.track) state.settings.music.paused = true;
  } else if (broadcastSafeMode && !isMusicEligible(savedTrack)) {
    const playable = playableMusicTracks();
    state.settings.music.track = playable[0]?.id || '';
    if (!state.settings.music.track) state.settings.music.paused = true;
  }
}

// Broadcast eligibility summary: blocked media stays on disk and in the audit.
if (broadcastSafeMode) {
  const eligibleBackgrounds = BACKGROUNDS.images.filter((img) => img.copyright?.eligible).length;
  const eligibleTracks = MUSIC.allTracks.filter((track) => track.copyright?.eligible).length;
  console.log(
    `[Copyright] Safe Mode ON — ${eligibleBackgrounds}/${BACKGROUNDS.images.length} backgrounds and ${eligibleTracks}/${MUSIC.allTracks.length} music files are eligible for broadcast.`
  );
} else {
  console.warn('[Copyright] Safe Mode OFF — blocked assets can be selected explicitly by an administrator.');
}

// Prayer congregation is live-session state only: nothing is written to disk.
const congregation = new Congregation();
congregation.configure(state.settings.congregation);
state.settings.congregation = { ...congregation.getPayload().settings };
congregation.onChange = (payload, meta) => {
  broadcastNotification('congregation.state', {
    ...payload,
    reason: meta.reason,
    changedId: meta.id || null,
    changedSource: meta.source || null
  });
};

let saveTimer = null;
function saveState() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => {
    const payload = {
      candlesLit: state.candlesLit,
      prayerCount: state.prayerCount,
      amenCount: state.amenCount,
      blessingsCount: state.blessingsCount,
      verseCount: state.verseCount,
      giftCount: state.giftCount,
      followCount: state.followCount,
      shareCount: state.shareCount,
      likeCount: state.likeCount,
      totalMerit: state.totalMerit,
      activeCandles: state.activeCandles,
      community: state.community,
      featuredVerse: state.featuredVerse,
      prayerRequests: state.prayerRequests.slice(0, 60),
      chatFeed: state.chatFeed.slice(0, 12),
      recentEvents: state.recentEvents.slice(0, 20),
      showHistory: (state.showHistory || []).slice(0, 20),
      quizRecent: (state.quizRecent || []).slice(0, 50),
      settings: state.settings
    };
    fs.promises.writeFile(STATE_FILE, JSON.stringify(payload, null, 2), 'utf8').catch((err) => {
      console.error('[State] Save failed:', err.message);
    });
  }, 1000);
}

// ============================================================================
// 5. TEXT SANITISERS & HELPERS
// ============================================================================
const WEIRD_SPAM_RE = /[\u{12000}-\u{1254F}\uFDFD\u2800-\u28FF\u2580-\u259F]|[\u0300-\u036F]{3,}/u;
const BRACKET_EMOTE_RE = /\[[^\]]{1,32}\]/g;
const CONTROL_RE = /[\u0000-\u001F\u007F]/g;
const URL_RE = /(https?:\/\/\S+|www\.\S+|\S+@\S+\.\S+)/gi;
const LONG_DIGITS_RE = /(?:\+?\d[\d\s().-]{5,}\d)/g;
const PROFANITY_RE = /\b(f+u+c+k+|sh[i1]t+|b[i1]tch|c+u+n+t+|a+s+s+h*o*l+e+|d[i1]ck|bastard|whore|slut|porn)\b/i;

function clampNumber(value, min, max, fallback) {
  const num = Number(value);
  if (!Number.isFinite(num)) return fallback;
  return Math.max(min, Math.min(max, num));
}

function stripHtml(input) {
  return String(input || '').replace(/<[^>]*>/g, ' ');
}

function baseClean(input, maxLength) {
  let text = String(input || '')
    .normalize('NFKC')
    .normalize('NFC')
    .replace(CONTROL_RE, ' ')
    .replace(BRACKET_EMOTE_RE, ' ')
    .replace(URL_RE, ' ')
    .replace(LONG_DIGITS_RE, ' ')
    .replace(/\s+/g, ' ')
    .trim();
  if (maxLength && text.length > maxLength) text = text.slice(0, maxLength);
  return text;
}

function isBlockedContent(raw) {
  if (!raw) return true;
  const text = String(raw);
  if (WEIRD_SPAM_RE.test(text)) return true;
  if (PROFANITY_RE.test(text)) return true;
  const configured = (CONFIG.moderation && CONFIG.moderation.blockedWords) || [];
  const lowered = text.toLowerCase();
  return configured.some((word) => word && lowered.includes(String(word).toLowerCase()));
}

function sanitizeDisplayName(rawName) {
  const cleaned = baseClean(stripHtml(rawName), 40)
    .replace(/[^\p{L}\p{N}\s._'’-]/gu, ' ')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, 26);
  const letters = cleaned.match(/[\p{L}]/gu) || [];
  if (letters.length < 1 || isBlockedContent(cleaned)) return 'Friend';
  return cleaned;
}

/** Short, privacy-conscious name used on screen ("Sarah J." -> "Sarah"). */
function firstNameForDisplay(name) {
  const cleaned = sanitizeDisplayName(name);
  const first = cleaned.split(/\s+/)[0].replace(/[._-]+$/, '');
  return (first || 'Friend').slice(0, 22);
}

const PRAYER_PREFIX_RE = /^(please\s+)?(pray\s+for(\s+(me|us))?|prayer\s+request(\s+please)?|prayers?\s+please|i\s+need\s+prayer)\b[\s,.:!-]*/i;

function sanitizePrayerText(rawText) {
  let text = baseClean(stripHtml(rawText), 300);
  // Remove only the leading request phrase, so "pray for my family" keeps "my family".
  text = text
    .replace(PRAYER_PREFIX_RE, '')
    .replace(/^(please\s+)?for\s+/i, '')
    .replace(/^(and|please)\s+/i, '')
    .replace(/[,.]?\s*please$/i, '')
    .replace(/([.,!?;:])\1+/g, '$1')
    .replace(/(.)\1{3,}/gi, '$1$1')
    .replace(/@\S+/g, ' ')
    .replace(/\s+/g, ' ')
    .replace(/^[.,!?;:\s-]+|[.,!?;:\s-]+$/g, '')
    .trim();
  if (text.length > CONFIG.prayer.maxLength) {
    text = `${text.slice(0, CONFIG.prayer.maxLength).trim()}…`;
  }
  const letters = text.match(/[\p{L}]/gu) || [];
  if (letters.length < 3 || isBlockedContent(text)) return '';
  return text;
}

function detectLanguage(text) {
  if (!text) return CONFIG.language.default;
  if (/[ăâđêôơưĂÂĐÊÔƠƯáàảãạấầẩẫậắằẳẵặéèẻẽẹếềểễệíìỉĩịóòỏõọốồổỗộớờởỡợúùủũụứừửữựýỳỷỹỵ]/u.test(text)) {
    return 'vi';
  }
  return 'en';
}

function shortNumber(value) {
  return Number(value || 0).toLocaleString('en-US');
}

// ============================================================================
// 6. COMMUNITY + PUBLIC STATE
// ============================================================================
function recordMember(user, uniqueId, avatar, meritDelta = 0, extras = {}) {
  const displayName = sanitizeDisplayName(user || uniqueId);
  const key = String(uniqueId || displayName).slice(0, 40);
  if (!state.community[key]) {
    state.community[key] = {
      name: displayName,
      uniqueId: uniqueId || '',
      avatar: avatar || '',
      merit: 0,
      prayers: 0,
      candles: 0,
      gifts: 0,
      lastWish: '',
      lastSeen: new Date().toISOString()
    };
  }
  const member = state.community[key];
  member.name = displayName;
  if (avatar) member.avatar = avatar;
  member.merit += meritDelta;
  member.prayers += Number(extras.prayers || 0);
  member.candles += Number(extras.candles || 0);
  member.gifts += Number(extras.gifts || 0);
  if (extras.wish) member.lastWish = extras.wish;
  member.lastSeen = new Date().toISOString();
  state.totalMerit += meritDelta;

  const keys = Object.keys(state.community);
  if (keys.length > 600) {
    keys
      .sort((a, b) => (state.community[a].merit || 0) - (state.community[b].merit || 0))
      .slice(0, 100)
      .forEach((stale) => delete state.community[stale]);
  }
  return member;
}

function getLeaderboard(limit = 6) {
  return Object.values(state.community)
    .sort((a, b) => b.merit - a.merit)
    .slice(0, limit)
    .map((member, index) => ({
      rank: index + 1,
      name: member.name,
      uniqueId: member.uniqueId,
      avatar: member.avatar || '',
      merit: member.merit || 0,
      prayers: member.prayers || 0,
      candles: member.candles || 0,
      lastWish: member.lastWish || '',
      // Legacy field kept for existing consumers.
      incense: member.candles || 0
    }));
}

function pushEventLog(event) {
  const entry = {
    id: `evt_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`,
    timestamp: new Date().toISOString(),
    ...event
  };
  state.recentEvents.unshift(entry);
  if (state.recentEvents.length > 30) state.recentEvents.length = 30;
  return entry;
}

function publicPrayerRequests() {
  return state.prayerRequests
    .filter((req) => req.status !== 'removed')
    .slice(0, 40)
    .map((req) => ({
      id: req.id,
      name: req.name,
      displayName: req.displayName,
      text: req.text,
      status: req.status,
      source: req.source,
      createdAt: req.createdAt,
      approvedAt: req.approvedAt || null,
      uniqueId: req.uniqueId || ''
    }));
}

function currentPrayer() {
  const visible = state.prayerRequests.filter((req) => req.status === 'approved' && req.displayedAt);
  if (visible.length === 0) return null;
  const latest = visible[0];
  const payload = buildPrayerPayload(latest);
  return {
    id: latest.id,
    name: latest.displayName,
    text: latest.text,
    ask: payload.ask,
    community: payload.community,
    createdAt: latest.displayedAt
  };
}

function chatFeedForClient() {
  return state.chatFeed.slice(0, 8).map((item) => ({
    id: item.id,
    user: item.user,
    text: item.text,
    avatar: item.avatar || '',
    at: item.at
  }));
}

function getPublicState() {
  const leaderboard = getLeaderboard(8);
  return {
    brand: BRAND,
    theme: CONFIG.theme,
    candlesLit: state.candlesLit,
    prayerCount: state.prayerCount,
    amenCount: state.amenCount,
    blessingsCount: state.blessingsCount,
    verseCount: state.verseCount,
    giftCount: state.giftCount,
    followCount: state.followCount,
    shareCount: state.shareCount,
    likeCount: state.likeCount,
    totalMerit: state.totalMerit,
    activeCandles: state.activeCandles,
    communityCount: Object.keys(state.community).length,
    featuredVerse: state.featuredVerse,
    leaderboard,
    prayerRequests: publicPrayerRequests(),
    currentPrayer: currentPrayer(),
    chatFeed: chatFeedForClient(),
    recentEvents: state.recentEvents.slice(0, 12),
    settings: state.settings,
    show: showPayload(),
    quiz: quizPayload(),
    congregation: congregation.getPayload(),
    copyright: (() => {
      const audit = copyrightAudit.get();
      return audit ? { generatedAt: audit.generatedAt, counts: audit.counts } : null;
    })(),
    copyrightSafeMode: broadcastSafeMode,
    broadcastSafety: (() => {
      const safety = getBroadcastSafetyPayload();
      return { available: safety.available, counts: safety.counts };
    })(),
    tiktok: state.tiktok,
    tts: ttsManager ? ttsManager.getStatus() : { ready: false, status: 'starting' },
    schedule: (() => {
      if (!smartSchedule) return null;
      const payload = schedulePayload();
      return {
        id: payload.current?.id || null,
        label: payload.current?.label || null,
        mode: payload.mode,
        timezone: payload.timezone,
        localTime: payload.local?.clock12 || null,
        remainingSeconds: payload.remainingSeconds,
        next: payload.next || null,
        override: payload.override
          ? { programId: payload.override.programId, remainingSeconds: payload.override.remainingSeconds }
          : null
      };
    })(),
    backgrounds: {
      current: state.settings.background.current,
      categories: BACKGROUNDS.categories,
      count: BACKGROUNDS.images.length,
      eligibleCount: BACKGROUNDS.images.filter((img) => img.copyright?.eligible).length
    },
    // ---- Legacy aliases (unchanged keys for existing RPC/OBS consumers) ----
    totalIncense: state.candlesLit,
    woodenFishHits: state.amenCount,
    bellRings: state.blessingsCount,
    lanternCount: state.prayerCount,
    fortuneCount: state.verseCount,
    activeIncenseSticks: state.activeCandles,
    offerings: {
      candle: state.candlesLit,
      cross: state.blessingsCount,
      bible: state.verseCount,
      celebration: state.giftCount,
      // Legacy keys retained for older consumers.
      lotus: state.candlesLit,
      fruit: state.prayerCount,
      lamp: state.verseCount,
      dragon: state.giftCount
    }
  };
}

// ============================================================================
// 7. PRAYER REQUEST QUEUE
// ============================================================================
const prayerCooldowns = new Map();

function prayerQueueCount() {
  return state.prayerRequests.filter((req) => req.status !== 'removed' && req.status !== 'hidden').length;
}

function trimPrayerQueue() {
  const max = state.settings.prayer.maxQueue || 30;
  if (state.prayerRequests.length > max) {
    state.prayerRequests = state.prayerRequests.slice(0, max);
  }
}

function buildPrayerPayload(request) {
  const vars = {
    name: request.displayName,
    text: request.text ? `“${request.text}”` : 'a personal need'
  };
  const displayPool = messageLibrary.templateList('prayerRequestDisplay');
  const matchingTemplates = displayPool.filter((template) => (
    request.text ? template.includes('{text}') : !template.includes('{text}')
  ));
  const askTemplate = (matchingTemplates.length > 0 ? matchingTemplates : displayPool)[
    Math.floor(Math.random() * (matchingTemplates.length > 0 ? matchingTemplates.length : displayPool.length))
  ];
  const ask = askTemplate
    ? messageLibrary.render(askTemplate, vars)
    : `${request.displayName} is asking for prayers.`;
  const community = messageLibrary.template('prayerRequestCommunity', vars)
    || `Let us keep ${request.displayName} in our prayers.`;
  const ttsText = messageLibrary.template('prayerRequestTts', vars)
    || `${request.displayName} is asking for prayers. Let us keep ${request.displayName} in our prayers.`;
  return { ask, community, ttsText };
}

function displayPrayerRequest(request) {
  if (!request || state.settings.prayer.paused) return null;
  request.status = 'approved';
  request.approvedAt = request.approvedAt || new Date().toISOString();
  request.displayedAt = new Date().toISOString();
  // An approved request places a small prayer symbol above the viewer's seat.
  congregation.markPrayer({
    uniqueId: request.uniqueId,
    // Only a genuine TikTok request may mark a real seat; admin/test entries stay visual-free.
    simulated: request.source !== 'tiktok'
  });

  const payload = buildPrayerPayload(request);
  const event = pushEventLog({
    type: 'sendPrayer',
    kind: 'prayerRequest',
    user: request.name,
    uniqueId: request.uniqueId || '',
    avatar: request.avatar || '',
    wish: request.text,
    prayerText: payload.ask,
    communityText: payload.community,
    simulated: request.source === 'simulation',
    ttsText: state.settings.ttsEnabled ? payload.ttsText.slice(0, 120) : '',
    ttsLang: 'en',
    merit: 2
  });

  saveState();
  // A prayer announcement owns the room; engagement reminders wait their turn.
  if (state.settings.ttsEnabled) engagementScheduler?.hold(15000);
  broadcastNotification('prayer.request', {
    request: {
      id: request.id,
      name: request.displayName,
      text: request.text,
      at: request.displayedAt
    },
    ask: payload.ask,
    community: payload.community,
    event,
    state: getPublicState()
  });
  return event;
}

function addPrayerRequest(params = {}) {
  const rawName = params.name || params.user;
  const name = sanitizeDisplayName(rawName);
  const text = sanitizePrayerText(params.text || params.wish || params.prayer || '');
  if (!name && !text) return null;
  if (text && isBlockedContent(text)) return null;

  const uniqueId = String(params.uniqueId || '').slice(0, 60);
  const now = Date.now();
  const source = params.source || 'tiktok';

  if (source === 'tiktok' && uniqueId) {
    const last = prayerCooldowns.get(uniqueId) || 0;
    const cooldownMs = (state.settings.prayer.cooldownSeconds || 30) * 1000;
    if (now - last < cooldownMs) return null;
    prayerCooldowns.set(uniqueId, now);
    if (prayerCooldowns.size > 800) {
      prayerCooldowns.delete(prayerCooldowns.keys().next().value);
    }
  }

  const duplicate = state.prayerRequests.some(
    (req) => req.text && req.text.toLowerCase() === text.toLowerCase()
      && now - new Date(req.createdAt).getTime() < 5 * 60 * 1000
  );
  if (text && duplicate) return null;

  const request = {
    id: `prayer_${now}_${Math.random().toString(36).slice(2, 6)}`,
    name,
    displayName: firstNameForDisplay(name),
    uniqueId,
    avatar: state.settings.prayer.showAvatar ? params.avatar || '' : '',
    text,
    status: state.settings.prayer.autoApprove ? 'approved' : 'pending',
    source,
    createdAt: new Date(now).toISOString(),
    approvedAt: state.settings.prayer.autoApprove ? new Date(now).toISOString() : null,
    displayedAt: null
  };

  state.prayerRequests.unshift(request);
  trimPrayerQueue();
  state.prayerCount += 1;
  recordMember(name, uniqueId, params.avatar, 2, { prayers: 1, wish: text });

  if (request.status === 'approved' && !state.settings.prayer.paused) {
    displayPrayerRequest(request);
  } else {
    saveState();
    broadcastNotification('prayer.state', { requests: publicPrayerRequests(), state: getPublicState() });
  }
  return request;
}

function approvePrayerRequest(id) {
  const request = state.prayerRequests.find((req) => req.id === id);
  if (!request) throw new Error('Prayer request not found');
  request.status = 'pending';
  displayPrayerRequest(request);
  broadcastNotification('prayer.state', { requests: publicPrayerRequests(), state: getPublicState() });
  return { request, state: getPublicState() };
}

function hidePrayerRequest(id) {
  const request = state.prayerRequests.find((req) => req.id === id);
  if (!request) throw new Error('Prayer request not found');
  request.status = 'hidden';
  request.hiddenAt = new Date().toISOString();
  saveState();
  const payload = { requests: publicPrayerRequests(), state: getPublicState() };
  broadcastNotification('prayer.state', payload);
  broadcastNotification('prayer.hide', { id });
  return payload;
}

function removePrayerRequest(id) {
  const before = state.prayerRequests.length;
  state.prayerRequests = state.prayerRequests.filter((req) => req.id !== id);
  saveState();
  const payload = { requests: publicPrayerRequests(), state: getPublicState() };
  broadcastNotification('prayer.state', payload);
  broadcastNotification('prayer.hide', { id });
  return { removed: before !== state.prayerRequests.length, ...payload };
}

function clearPrayerRequests() {
  state.prayerRequests = [];
  state.prayerCount = Math.max(0, state.prayerCount);
  saveState();
  const payload = { requests: [], state: getPublicState() };
  broadcastNotification('prayer.state', payload);
  broadcastNotification('prayer.hide', { id: '*' });
  return payload;
}

// ============================================================================
// 8. INTERACTION RITUALS (legacy RPC names preserved)
// ============================================================================
const Rituals = {
  /** temple.burnIncense -> light prayer candles */
  burnIncense(params = {}) {
    const name = sanitizeDisplayName(params.user);
    const uniqueId = String(params.uniqueId || '');
    const count = clampNumber(params.count, 1, 9, 1);
    const wish = sanitizePrayerText(params.wish || '');
    const merit = count * 3;

    state.candlesLit += count;
    state.activeCandles = Math.min(24, state.activeCandles + count);
    const member = recordMember(name, uniqueId, params.avatar, merit, {
      candles: count,
      wish
    });

    const event = pushEventLog({
      type: 'burnIncense',
      kind: 'candle',
      user: member.name,
      uniqueId: member.uniqueId,
      avatar: member.avatar,
      count,
      merit,
      wish,
      simulated: Boolean(params.simulated),
      message: `${count} prayer ${count === 1 ? 'candle' : 'candles'} lit`,
      ttsText: ''
    });

    saveState();
    broadcastNotification('temple.event', { event, state: getPublicState() });
    return { event, state: getPublicState() };
  },

  /** temple.strikeWoodenFish -> AMEN pulse (likes) */
  strikeWoodenFish(params = {}) {
    const name = sanitizeDisplayName(params.user);
    const uniqueId = String(params.uniqueId || '');
    const count = clampNumber(params.count, 1, 50, 1);
    const merit = count;

    state.amenCount += count;
    const member = recordMember(name, uniqueId, params.avatar, merit);

    const event = pushEventLog({
      type: 'strikeWoodenFish',
      kind: 'amen',
      user: member.name,
      uniqueId: member.uniqueId,
      avatar: member.avatar,
      count,
      merit,
      simulated: Boolean(params.simulated),
      message: 'Amen',
      ttsText: ''
    });

    saveState();
    broadcastNotification('temple.event', { event, state: getPublicState() });
    return { event, state: getPublicState() };
  },

  /** temple.ringBell -> blessing / gratitude chime */
  ringBell(params = {}) {
    const name = sanitizeDisplayName(params.user);
    const uniqueId = String(params.uniqueId || '');
    const count = clampNumber(params.count, 1, 9, 1);
    const kind = params.kind || 'blessing';
    const wish = sanitizePrayerText(params.wish || '');
    const merit = count * 5;

    state.blessingsCount += count;
    const member = recordMember(name, uniqueId, params.avatar, merit, { wish });
    const message = params.message || messageLibrary.template('gratitude') || 'Thank you for being here.';

    const event = pushEventLog({
      type: 'ringBell',
      kind,
      user: member.name,
      uniqueId: member.uniqueId,
      avatar: member.avatar,
      count,
      merit,
      wish,
      simulated: Boolean(params.simulated),
      message,
      ttsText: params.readTts && state.settings.ttsEnabled ? message : '',
      ttsLang: 'en'
    });

    saveState();
    broadcastNotification('temple.event', { event, state: getPublicState() });
    return { event, state: getPublicState() };
  },

  /** temple.sendPrayer -> submit a prayer request */
  sendPrayer(params = {}) {
    const request = addPrayerRequest({
      name: params.user || params.name,
      uniqueId: params.uniqueId,
      avatar: params.avatar,
      text: params.wish || params.text,
      source: params.source || 'rpc'
    });
    if (!request) {
      return { event: null, state: getPublicState(), skipped: true };
    }
    const event = state.recentEvents.find(
      (evt) => evt.kind === 'prayerRequest' && evt.wish === request.text
    ) || pushEventLog({
      type: 'sendPrayer',
      kind: 'prayerRequest',
      user: request.name,
      uniqueId: request.uniqueId,
      avatar: request.avatar,
      wish: request.text,
      prayerText: `${request.displayName} is asking for prayers.`,
      ttsText: '',
      merit: 2
    });
    return { event, request, state: getPublicState() };
  },

  /** temple.offerGift -> Christian tiered gift acknowledgement */
  offerGift(params = {}) {
    const name = sanitizeDisplayName(params.user);
    const uniqueId = String(params.uniqueId || '');
    const coins = clampNumber(params.coins, 1, 1000000, 1);
    const giftName = baseClean(stripHtml(params.giftName), 60) || 'a gift';
    const quantity = clampNumber(params.quantity, 1, 999, 1);
    const giftLabel = quantity > 1 ? `${quantity}x ${giftName}` : giftName;
    const tiers = CONFIG.giftTiers;
    const tier = coins >= tiers.large ? 'large' : coins >= tiers.medium ? 'medium' : 'small';
    const multiplier = tier === 'large' ? 12 : tier === 'medium' ? 6 : 3;
    const merit = Math.max(1, Math.round(coins * multiplier));
    const giftSettings = state.settings.gifts || {};
    const announce = giftSettings.announce !== false;
    const personalThanks = messageLibrary.pickFromList(
      messageLibrary.templateList('giftPersonal'),
      // Drop a trailing period so the thank-you reads as one natural sentence.
      { name: name === 'Friend' ? 'friend' : name.replace(/\.+$/, ''), gift: giftName, quantity }
    );
    const message = personalThanks
      || messageLibrary.template(`giftThanks.${tier}`)
      || 'Thank you for supporting our prayer community.';

    state.giftCount += 1;
    state.candlesLit += tier === 'small' ? 1 : 2;
    state.activeCandles = Math.min(24, state.activeCandles + 1);
    const member = recordMember(name, uniqueId, params.avatar, merit, { gifts: 1 });
    congregation.markGift({
      uniqueId: member.uniqueId,
      giftName,
      simulated: Boolean(params.simulated) || params.source !== 'tiktok'
    });

    // A spoken gift thank-you owns the room; reminders wait their turn.
    if (announce && giftSettings.tts !== false && state.settings.ttsEnabled) {
      engagementScheduler?.hold(15000);
    }

    const event = pushEventLog({
      type: tier === 'large' ? 'grandCeremony' : 'offerGift',
      kind: 'gift',
      tier,
      user: member.name,
      uniqueId: member.uniqueId,
      avatar: member.avatar,
      giftType: params.giftType || tier,
      giftName: giftLabel,
      giftBaseName: giftName,
      quantity,
      coins,
      merit,
      simulated: Boolean(params.simulated),
      announce,
      message,
      ttsText: announce && state.settings.ttsEnabled && giftSettings.tts !== false ? message : '',
      ttsLang: 'en'
    });

    saveState();
    broadcastNotification('temple.event', { event, state: getPublicState() });
    return { event, tier, state: getPublicState() };
  },

  /** temple.grandCeremony -> large celebration (kept for compatibility) */
  grandCeremony(params = {}) {
    return this.offerGift({
      ...params,
      coins: Math.max(CONFIG.giftTiers.large, Number(params.coins) || CONFIG.giftTiers.large),
      giftName: params.giftName || 'A gift of encouragement'
    });
  },

  /** temple.drawFortune -> Scripture card (verified verses only) */
  drawFortune(params = {}) {
    const name = sanitizeDisplayName(params.user);
    const uniqueId = String(params.uniqueId || '');
    const verse = messageLibrary.bibleVerse();
    if (!verse) throw new Error('No Bible verses configured');
    const merit = 2;

    state.verseCount += 1;
    state.featuredVerse = verse;
    const member = recordMember(name, uniqueId, params.avatar, merit, { wish: verse.reference });
    const ttsText = state.settings.ttsEnabled
      ? `${verse.text} ${verse.reference.replace(/\(KJV\)/i, '').replace(':', ' verse ')}.`
      : '';

    const event = pushEventLog({
      type: 'drawFortune',
      kind: 'verse',
      user: member.name,
      uniqueId: member.uniqueId,
      avatar: member.avatar,
      verse: { text: verse.text, reference: verse.reference },
      // Legacy fortune shape retained so old consumers do not break.
      fortune: {
        number: state.verseCount,
        rank: 'Scripture',
        title: verse.reference,
        poem: verse.text,
        meaning: 'A word of encouragement from Scripture.'
      },
      merit,
      simulated: Boolean(params.simulated),
      message: `${verse.text} — ${verse.reference}`,
      ttsText,
      ttsLang: 'en'
    });

    saveState();
    broadcastNotification('temple.event', { event, state: getPublicState() });
    return { event, state: getPublicState() };
  },

  updateSettings(params = {}) {
    return applySettingsUpdate(params);
  },

  resetMerit() {
    state.candlesLit = 0;
    state.prayerCount = 0;
    state.amenCount = 0;
    state.blessingsCount = 0;
    state.verseCount = 0;
    state.giftCount = 0;
    state.followCount = 0;
    state.shareCount = 0;
    state.likeCount = 0;
    state.totalMerit = 0;
    state.activeCandles = 0;
    state.community = {};
    state.prayerRequests = [];
    state.chatFeed = [];
    state.recentEvents = [];
    saveState();
    broadcastNotification('temple.state', getPublicState());
    return getPublicState();
  }
};

// ============================================================================
// 9. SETTINGS / BACKGROUND ROTATION
// ============================================================================
function getBroadcastSafetyPayload() {
  return broadcastSafety.summary(
    [...BACKGROUNDS.images, ...OVERLAY_IMAGES],
    MUSIC.allTracks,
    broadcastSafeMode
  );
}

function musicCatalogPayload() {
  return {
    tracks: playableMusicTracks(),
    library: MUSIC.allTracks,
    settings: state.settings.music,
    meta: MUSIC.libraryMeta,
    safety: getBroadcastSafetyPayload()
  };
}

/** If the selected track vanished, was disabled or was blocked, move to the first playable one. */
function repairMusicSelection() {
  const music = state.settings.music;
  if (!music) return false;
  const playable = playableMusicTracks();
  if (playable.length === 0) {
    if (!music.track && music.paused) return false;
    music.track = '';
    music.paused = true;
    return true;
  }
  if (playable.some((track) => track.id === music.track)) return false;
  if (music.track) {
    const previous = MUSIC.libraryById.get(music.track) || MUSIC.byId.get(music.track);
    const decision = broadcastSafety.music(previous?.file || music.track, { safeMode: broadcastSafeMode });
    console.warn('[Copyright] Skipped music selection:', music.track, decision.reason);
  }
  music.track = playable[0].id;
  return true;
}

function musicRescanPayload(result) {
  return {
    ...musicCatalogPayload(),
    scan: {
      found: result.found,
      added: result.addedCount,
      removed: result.removedCount,
      updated: result.updatedCount,
      addedFiles: result.added,
      removedFiles: result.removed,
      updatedFiles: result.updated,
      errors: result.errors,
      scannedAt: result.scannedAt
    }
  };
}

function publishMusicLibrary(payload) {
  broadcastNotification('music.library.updated', payload);
}

function musicOrder() {
  return playableMusicTracks().map((track) => track.id);
}

function pickAdjacentTrack(direction = 1) {
  const order = musicOrder();
  if (order.length === 0) return null;
  const current = state.settings.music.track;
  if (state.settings.music.shuffle && order.length > 1) {
    const pool = order.filter((id) => id !== current);
    return pool[Math.floor(Math.random() * pool.length)];
  }
  const index = order.indexOf(current);
  const next = (index + (direction > 0 ? 1 : -1) + order.length) % order.length;
  return order[next];
}

/** Mutates settings.music from a partial patch; returns true when anything changed. */
function patchMusicSettings(patch = {}) {
  const music = state.settings.music;
  if (!music || !patch || typeof patch !== 'object') return false;
  const before = JSON.stringify(music);

  if (patch.track !== undefined) {
    const id = String(patch.track || '');
    if (id && !MUSIC.byId.has(id)) {
      if (MUSIC.libraryById.has(id)) throw new Error('That track is disabled. Enable it in the music library first.');
      throw new Error(`Unknown music track: ${id}`);
    }
    if (id) {
      const decision = broadcastSafety.music(MUSIC.byId.get(id)?.file || id, { safeMode: broadcastSafeMode });
      if (!decision.selectable) {
        console.warn('[Copyright] Blocked music selection:', id, decision.reason);
        throw new Error(`Copyright Safe Mode blocks that track: ${decision.reason}`);
      }
    }
    if (id) {
      music.track = id;
      // Selecting a track is an explicit request to hear it.
      music.paused = false;
      if (!music.enabled) music.enabled = true;
    }
  }
  if (typeof patch.enabled === 'boolean') {
    music.enabled = patch.enabled;
    if (patch.enabled) music.paused = false;
  }
  if (typeof patch.paused === 'boolean') {
    music.paused = patch.paused;
    if (!patch.paused) music.enabled = true;
  }
  if (typeof patch.autoplay === 'boolean') music.autoplay = patch.autoplay;
  if (typeof patch.shuffle === 'boolean') music.shuffle = patch.shuffle;
  if (patch.repeat === 'off' || patch.repeat === 'one' || patch.repeat === 'all') {
    music.repeat = patch.repeat;
  }
  if (patch.volume !== undefined) music.volume = clampNumber(patch.volume, 0, 1, music.volume);
  if (patch.duckVolume !== undefined) {
    music.duckVolume = clampNumber(patch.duckVolume, 0, 0.5, music.duckVolume);
  }
  return JSON.stringify(music) !== before;
}

function applyMusicUpdate(params = {}) {
  patchMusicSettings(params);
  saveState();
  broadcastNotification('music.state', { settings: state.settings.music });
  broadcastNotification('temple.state', getPublicState());
  return musicCatalogPayload();
}

function refreshBroadcastMedia() {
  applyMusicCatalog(MUSIC_LIBRARY.readCatalog());
  BACKGROUNDS.images = broadcastSafety.annotateImages(BACKGROUNDS.images, broadcastSafeMode);

  if (broadcastSafeMode && state.settings.background.category !== 'all') {
    const hasEligible = BACKGROUNDS.images.some(
      (img) => img.category === state.settings.background.category && img.copyright?.eligible
    );
    if (!hasEligible) state.settings.background.category = 'all';
  }

  if (broadcastSafeMode) {
    const current = BACKGROUNDS.images.find((img) => img.url === state.settings.background.current);
    if (!current || !current.copyright?.eligible) {
      const fallback = BACKGROUNDS.images.find((img) => img.copyright?.eligible);
      if (fallback) {
        setCurrentBackground(fallback.url, { rotate: false });
      } else {
        console.warn('[Copyright] No verified background available; clearing the stage background.');
        state.settings.background.current = '';
        broadcastNotification('stage.background', {
          url: '',
          clear: true,
          reason: 'No VERIFIED background is available in Copyright Safe Mode'
        });
      }
    }
  }

  const musicChanged = repairMusicSelection();
  configureBackgroundRotation();
  saveState();
  if (musicChanged) broadcastNotification('music.state', { settings: state.settings.music });
  return getBroadcastSafetyPayload();
}

/**
 * Rebuild the stage catalog from disk without restarting the server. Used after
 * an image-library scan. Keeps the current background when its file still
 * exists; otherwise falls back to another broadcast-eligible image.
 */
function reloadBackgroundCatalog() {
  const catalog = loadBackgroundImages();
  BACKGROUNDS.images = catalog.images;
  BACKGROUNDS.categories = catalog.categories;

  if (state.settings.background.category !== 'all'
    && !BACKGROUNDS.categories.includes(state.settings.background.category)) {
    state.settings.background.category = 'all';
  }
  if (broadcastSafeMode && state.settings.background.category !== 'all') {
    const hasEligible = BACKGROUNDS.images.some(
      (img) => img.category === state.settings.background.category && img.copyright?.eligible
    );
    if (!hasEligible) state.settings.background.category = 'all';
  }

  const previousUrl = state.settings.background.current;
  const previous = BACKGROUNDS.images.find((img) => img.url === previousUrl);
  const pool = BACKGROUNDS.images.filter((img) => !broadcastSafeMode || img.copyright?.eligible);
  const selected = previous || pool[0] || null;

  if (selected) {
    state.settings.background.current = selected.url;
    broadcastNotification('stage.background', {
      url: selected.url,
      category: selected.category,
      transitionMs: state.settings.background.transitionMs,
      source: previous ? 'catalog-refresh' : 'catalog-fallback',
      settings: state.settings.background
    });
  } else {
    state.settings.background.current = '';
    broadcastNotification('stage.background', {
      url: '',
      clear: true,
      reason: 'No broadcast-eligible background remains in the image library'
    });
  }

  configureBackgroundRotation();
  saveState();
  return {
    count: BACKGROUNDS.images.length,
    categories: BACKGROUNDS.categories,
    current: state.settings.background.current,
    previousExists: Boolean(previous),
    eligibleCount: BACKGROUNDS.images.filter((img) => img.copyright?.eligible).length
  };
}

/** Adds local URLs and the shared Copyright Safe Mode decision to a scan payload. */
function enrichImageLibrary(payload) {
  if (!payload) return payload;
  const images = (payload.images || []).map((image) => {
    const url = `/assets/christian/${image.file}`;
    const decision = broadcastSafety.image(url, { safeMode: broadcastSafeMode });
    return {
      ...image,
      url,
      status: decision.status,
      eligible: decision.eligible,
      blockReason: decision.eligible ? '' : decision.reason
    };
  });
  // Align the panel counters with the licensing audit: an image is "licensed"
  // only when Copyright Safe Mode can actually put it on the stage.
  const verified = images.filter((image) => image.status === 'VERIFIED').length;
  const totals = payload.totals
    ? { ...payload.totals, licensed: verified, needsReview: images.length - verified }
    : payload.totals;
  return { ...payload, images, totals };
}

function applyCopyrightSafeMode(enabled) {
  const next = Boolean(enabled);
  if (next === broadcastSafeMode) return getBroadcastSafetyPayload();
  state.settings.copyrightSafeMode = next;
  broadcastSafeMode = next;
  const safety = refreshBroadcastMedia();
  broadcastNotification('copyright.updated', { safety });
  broadcastNotification('temple.state', getPublicState());
  return safety;
}

/** Engagement reminders only speak to a room that actually has an audience. */
function engagementAudiencePresent() {
  if ((Number(state.tiktok?.viewerCount) || 0) > 0) return true;
  const payload = congregation && congregation.getPayload ? congregation.getPayload() : null;
  const seats = (payload?.participants || []).filter((participant) => participant.source !== 'demo');
  return seats.length > 0;
}

function engagementStatusPayload() {
  const status = engagementScheduler ? engagementScheduler.status() : { enabled: false, next: [] };
  return {
    ...status,
    viewers: Number(state.tiktok?.viewerCount) || 0,
    audiencePresent: engagementAudiencePresent(),
    narrationBusySeconds: Math.max(0, Math.ceil((narrationBusyUntil - Date.now()) / 1000)),
    defaults: ENGAGEMENT_DEFAULTS
  };
}

/**
 * Speaks one engagement reminder through the shared Piper + tts.play path.
 * Nothing is spoken while another announcement is in the room, and a failure
 * backs the scheduler off instead of hammering the voice engine.
 */
async function speakEngagementReminder(category = 'like', options = {}) {
  if (!engagementMessages || !ttsManager) return { ok: false, error: 'Narration is not ready yet.' };
  if (!state.settings.ttsEnabled) return { ok: false, skipped: 'narration is off' };
  if (Date.now() < farewellUntil) return { ok: false, skipped: 'the closing blessing is playing' };
  if (Date.now() < narrationBusyUntil) return { ok: false, skipped: 'another announcement is speaking' };
  if (!options.manual && !engagementAudiencePresent()) return { ok: false, skipped: 'no viewers watching' };
  const text = engagementMessages.pick(category);
  if (!text) return { ok: false, error: `No ${category} message configured.` };
  try {
    const result = await ttsManager.synthesize(text, { lang: 'en' });
    if (!result.ok) return { ok: false, error: result.error || 'Piper is unavailable' };
    inspectTtsAudio(result, `the ${category} reminder`);
    const durationSec = Math.max(2, Number(result.durationSec) || 8);
    // Welcome and prayer cues extend this; reminders never shorten the lock.
    narrationBusyUntil = Math.max(narrationBusyUntil, Date.now() + durationSec * 1000 + 2200);
    broadcastNotification('tts.play', {
      text,
      voice: result.voice,
      language: result.language,
      url: result.url,
      durationSec,
      source: 'engagement',
      engagement: true
    });
    return { ok: true, category, text, durationSec, manual: Boolean(options.manual) };
  } catch (err) {
    return { ok: false, error: err.message };
  }
}

function applySettingsUpdate(params = {}) {
  const settings = state.settings;
  if (typeof params.ttsEnabled === 'boolean') settings.ttsEnabled = params.ttsEnabled;
  if (params.ttsLanguage === 'en' || params.ttsLanguage === 'vi') settings.ttsLanguage = params.ttsLanguage;
  if (typeof params.enVoice === 'string') {
    const voice = resolveVoice(VOICES, 'en', params.enVoice);
    if (voice) settings.enVoice = voice.id;
  }
  if (typeof params.vnVoice === 'string') {
    const voice = resolveVoice(VOICES, 'vi', params.vnVoice);
    if (voice) settings.vnVoice = voice.id;
  }
  if (params.ttsVolume !== undefined) settings.ttsVolume = clampNumber(params.ttsVolume, 0, 1, settings.ttsVolume);
  if (params.ttsRate !== undefined) settings.ttsRate = clampNumber(params.ttsRate, 0.6, 1.6, settings.ttsRate);
  // Background music: current object shape plus the legacy scalar aliases.
  if (params.music && typeof params.music === 'object') patchMusicSettings(params.music);
  if (params.musicVolume !== undefined) patchMusicSettings({ volume: params.musicVolume });
  if (typeof params.bgMusicEnabled === 'boolean') patchMusicSettings({ enabled: params.bgMusicEnabled });
  if (typeof params.sfxEnabled === 'boolean') settings.sfxEnabled = params.sfxEnabled;
  if (typeof params.autoSim === 'boolean') settings.autoSim = params.autoSim;
  if (params.autoSimIntervalMs !== undefined) {
    settings.autoSimIntervalMs = clampNumber(params.autoSimIntervalMs, 3000, 120000, settings.autoSimIntervalMs);
  }

  if (params.background && typeof params.background === 'object') {
    const bg = params.background;
    if (typeof bg.enabled === 'boolean') settings.background.enabled = bg.enabled;
    if (bg.intervalSeconds !== undefined) {
      settings.background.intervalSeconds = clampNumber(bg.intervalSeconds, 10, 3600, settings.background.intervalSeconds);
    }
    if (typeof bg.randomize === 'boolean') settings.background.randomize = bg.randomize;
    if (bg.transitionMs !== undefined) {
      settings.background.transitionMs = clampNumber(bg.transitionMs, 400, 6000, settings.background.transitionMs);
    }
    if (typeof bg.category === 'string') {
      let category = bg.category === 'all' || BACKGROUNDS.categories.includes(bg.category)
        ? bg.category
        : settings.background.category;
      if (broadcastSafeMode && category !== 'all') {
        const hasEligible = BACKGROUNDS.images.some(
          (img) => img.category === category && img.copyright?.eligible
        );
        if (!hasEligible) category = 'all';
      }
      settings.background.category = category;
    }
    if (typeof bg.sceneMatch === 'boolean') settings.background.sceneMatch = bg.sceneMatch;
  }

  if (params.prayer && typeof params.prayer === 'object') {
    if (typeof params.prayer.autoApprove === 'boolean') settings.prayer.autoApprove = params.prayer.autoApprove;
    if (typeof params.prayer.paused === 'boolean') settings.prayer.paused = params.prayer.paused;
    if (typeof params.prayer.interactionEnabled === 'boolean') {
      settings.prayer.interactionEnabled = params.prayer.interactionEnabled;
    }
    if (params.prayer.cooldownSeconds !== undefined) {
      settings.prayer.cooldownSeconds = clampNumber(params.prayer.cooldownSeconds, 5, 600, settings.prayer.cooldownSeconds);
    }
    if (params.prayer.maxQueue !== undefined) {
      settings.prayer.maxQueue = clampNumber(params.prayer.maxQueue, 5, 200, settings.prayer.maxQueue);
      trimPrayerQueue();
    }
  }

  if (params.engagement && typeof params.engagement === 'object') {
    settings.engagement = mergeEngagementSettings(settings.engagement, params.engagement);
    // New intervals restart the clocks instead of firing an old backlog.
    engagementScheduler?.refresh();
  }

  configureAutoSim(settings.autoSim);
  configureBackgroundRotation();
  saveState();
  broadcastNotification('music.state', { settings: settings.music });
  broadcastNotification('temple.state', getPublicState());
  return getPublicState();
}

// ============================================================================
// 10. AUTOMATED LIVE SHOW (welcome, Scripture, prayer, community, gratitude)
// ============================================================================
function showPayload() {
  const status = showProgram ? showProgram.status() : null;
  const history = (state.showHistory || []).slice(0, 12);
  if (!status) {
    return {
      enabled: Boolean(state.settings.show && state.settings.show.enabled),
      paused: Boolean(state.settings.show && state.settings.show.paused),
      welcomeEnabled: Boolean(state.settings.show && state.settings.show.welcomeEnabled),
      narration: Boolean(state.settings.show && state.settings.show.narration),
      theme: (state.settings.show && state.settings.show.theme) || 'auto',
      pace: (state.settings.show && state.settings.show.pace) || 1,
      themes: PRAYER_THEMES.map((theme) => ({ id: theme.id, label: theme.label })),
      history
    };
  }
  return {
    ...status,
    history,
    narrationBusySeconds: Math.max(0, Math.ceil((narrationBusyUntil - Date.now()) / 1000))
  };
}

/**
 * Verifies the WAV Piper just wrote. A header-valid but silent file is reported
 * once; narration itself is never replayed, so nothing speaks twice.
 */
function inspectTtsAudio(result, context = 'narration') {
  if (!result || !result.ok || !result.url) return null;
  const file = path.join(TTS_CACHE_DIR, path.basename(String(result.url)));
  const stats = wavStats(file);
  if (stats && stats.silent) {
    healthMonitor?.addIncident({
      component: 'tts',
      severity: 'warning',
      message: `Piper returned a silent WAV file for ${context}.`,
      action: 'Kept the stage silent rather than replaying a failure',
      result: `RMS ${stats.rms} · peak ${stats.peak}`
    });
  }
  return stats;
}

// ============================================================================
// 9b. FAREWELL SCREEN (OPERATOR-TRIGGERED CLOSING BLESSING)
// ============================================================================
// Messages live in config/farewell-messages.json. The browser only ever sends an
// id, so the text shown on the stage and read by Piper always comes from here.
const FAREWELL_LIBRARY_FILE = path.join(__dirname, 'config', 'farewell-messages.json');
const FAREWELL_FALLBACK = {
  id: 'until-we-meet-again',
  title: 'Until We Meet Again',
  eyebrow: 'FINAL BLESSING',
  paragraphs: [
    'Dear friends, as we come to the end of this time together, we want to thank each and every one of you for joining us in prayer.',
    'May God bless your families, strengthen your hearts, and fill your lives with peace, hope, and love.',
    'Remember, you are never alone. God is always with you.',
    'Thank you for praying with us today. Until we meet again, may the grace of our Lord Jesus Christ be with you all.'
  ],
  closing: 'God bless you. Amen.'
};
// Held while Piper synthesizes, then replaced by the real reading length.
const FAREWELL_SYNTHESIS_WINDOW_MS = 20000;
const FAREWELL_MIN_SCREEN_MS = 45000;

function normalizeFarewellMessages(raw) {
  const entries = Array.isArray(raw?.messages) ? raw.messages : [];
  const seen = new Set();
  const messages = [];
  entries.forEach((entry) => {
    const id = String(entry?.id || '').trim().toLowerCase();
    const title = String(entry?.title || '').trim();
    const paragraphs = (Array.isArray(entry?.paragraphs) ? entry.paragraphs : [])
      .map((paragraph) => String(paragraph || '').trim())
      .filter(Boolean);
    if (!id || !title || paragraphs.length === 0 || seen.has(id)) return;
    seen.add(id);
    const closing = String(entry?.closing || '').trim();
    messages.push({
      id,
      title,
      eyebrow: String(entry?.eyebrow || 'FINAL BLESSING').trim() || 'FINAL BLESSING',
      paragraphs,
      closing,
      text: [...paragraphs, closing].filter(Boolean).join(' ')
    });
  });
  return messages;
}

/** Loaded once at startup; a malformed or missing file falls back to the default. */
const FAREWELL_LIBRARY = (() => {
  let messages = [];
  let defaultId = FAREWELL_FALLBACK.id;
  try {
    const raw = JSON.parse(fs.readFileSync(FAREWELL_LIBRARY_FILE, 'utf8'));
    messages = normalizeFarewellMessages(raw);
    const wanted = String(raw?.default || '').trim().toLowerCase();
    if (wanted && messages.some((message) => message.id === wanted)) defaultId = wanted;
  } catch (err) {
    console.warn(`[Farewell] Library unavailable (${err.message}); using the built-in message.`);
  }
  if (messages.length === 0) messages = normalizeFarewellMessages({ messages: [FAREWELL_FALLBACK] });
  if (!messages.some((message) => message.id === defaultId)) defaultId = messages[0].id;
  console.log(`[Farewell] ${messages.length} closing message(s) registered · default ${defaultId}`);
  return { messages, defaultId };
})();

function farewellMessageById(id) {
  const wanted = String(id || FAREWELL_LIBRARY.defaultId).trim().toLowerCase();
  return FAREWELL_LIBRARY.messages.find((message) => message.id === wanted) || null;
}

/** Sanitised library for the dashboard — no filesystem paths, no extra fields. */
function farewellLibraryPayload() {
  return {
    default: FAREWELL_LIBRARY.defaultId,
    messages: FAREWELL_LIBRARY.messages.map((message) => ({
      id: message.id,
      title: message.title,
      eyebrow: message.eyebrow,
      paragraphs: message.paragraphs,
      closing: message.closing,
      text: message.text,
      characters: message.text.length
    }))
  };
}

function farewellPayload() {
  const active = farewellMessageById(farewellCue?.messageId);
  return {
    active: Date.now() < farewellUntil,
    cueId: farewellCue?.id || null,
    messageId: active?.id || FAREWELL_LIBRARY.defaultId,
    title: farewellCue?.title || active?.title || 'Until We Meet Again',
    endsAt: farewellUntil ? new Date(farewellUntil).toISOString() : null
  };
}

function buildFarewellCue(message) {
  return {
    id: `farewell-${Date.now().toString(36)}`,
    kind: 'farewell',
    messageId: message.id,
    eyebrow: message.eyebrow,
    title: message.title,
    body: message.paragraphs[0],
    note: message.closing,
    paragraphs: [...message.paragraphs, message.closing].filter(Boolean),
    ttsText: message.text,
    displayMs: FAREWELL_MIN_SCREEN_MS,
    at: new Date().toISOString()
  };
}

/**
 * Broadcasts the closing blessing to the Live Stage and narrates it through the
 * shared Piper queue. It never touches the TikTok connection, the show timer or
 * the background rotation — the operator ends the broadcast by hand afterwards.
 */
async function triggerFarewell(params = {}) {
  const now = Date.now();
  if (now < farewellUntil) {
    return {
      ok: false,
      alreadyPlaying: true,
      remainingSeconds: Math.ceil((farewellUntil - now) / 1000),
      error: 'A farewell is already playing on the Live Stage. Wait for it to finish before starting another.',
      farewell: farewellPayload()
    };
  }

  const requested = params.messageId === undefined || params.messageId === null || params.messageId === ''
    ? FAREWELL_LIBRARY.defaultId
    : String(params.messageId).trim().toLowerCase();
  const message = farewellMessageById(requested);
  if (!message) {
    return {
      ok: false,
      unknownMessage: true,
      error: `Unknown farewell message "${requested || '(empty)'}". Choose one from the library.`,
      messages: farewellLibraryPayload().messages.map((entry) => entry.id),
      farewell: farewellPayload()
    };
  }

  const cue = buildFarewellCue(message);
  farewellCue = cue;
  // Locked before the first await so a double click cannot queue two readings.
  farewellUntil = now + FAREWELL_SYNTHESIS_WINDOW_MS;

  state.showHistory = [
    {
      id: cue.id,
      kind: cue.kind,
      eyebrow: cue.eyebrow,
      title: cue.title,
      body: String(cue.body || '').slice(0, 260),
      at: cue.at,
      source: 'manual',
      simulated: false
    },
    ...(state.showHistory || []).filter((entry) => entry.id !== cue.id)
  ].slice(0, 20);
  lastPublishedCue = cue;
  lastPublishedAt = now;

  // Visual first: the stage should never wait on speech synthesis.
  broadcastNotification('show.farewell', {
    cue,
    messageId: message.id,
    text: message.text,
    paragraphs: cue.paragraphs,
    state: 'started',
    durationMs: FAREWELL_SYNTHESIS_WINDOW_MS,
    startedAt: cue.at
  });
  broadcastNotification('show.state', { show: showPayload() });
  saveState();

  let durationSec = 0;
  let error = null;
  try {
    const result = await ttsManager.synthesize(message.text, { lang: 'en' });
    if (result.ok) {
      inspectTtsAudio(result, 'the farewell message');
      durationSec = Math.max(2, Number(result.durationSec) || 40);
      narrationBusyUntil = Date.now() + durationSec * 1000 + 2200;
      broadcastNotification('tts.play', {
        text: message.text,
        voice: result.voice,
        language: result.language,
        url: result.url,
        durationSec,
        source: 'farewell'
      });
    } else {
      error = result.error || 'Piper is unavailable';
    }
  } catch (err) {
    error = err.message;
  }

  const screenMs = durationSec
    ? Math.max(FAREWELL_MIN_SCREEN_MS, durationSec * 1000 + 14000)
    : FAREWELL_MIN_SCREEN_MS;
  farewellUntil = Date.now() + screenMs;

  broadcastNotification('show.farewell', {
    cue,
    messageId: message.id,
    text: message.text,
    paragraphs: cue.paragraphs,
    state: error ? 'visual-only' : 'speaking',
    durationMs: screenMs,
    error
  });

  clearTimeout(farewellEndTimer);
  farewellEndTimer = setTimeout(() => {
    broadcastNotification('show.farewell', { cue, cueId: cue.id, state: 'ended' });
  }, screenMs);

  if (error) console.warn(`[Farewell] Narration unavailable: ${error}`);
  else console.log(`[Farewell] "${message.title}" on the stage for ${Math.round(screenMs / 1000)}s.`);

  return {
    ok: true,
    cue,
    messageId: message.id,
    title: message.title,
    text: message.text,
    displayMs: screenMs,
    narration: !error,
    error,
    farewell: farewellPayload()
  };
}

/** Sends a cue to the OBS stage, then narrates it through the shared TTS queue. */
async function publishShowCue(cue, { source = 'auto' } = {}) {
  if (!cue) return;
  if (cue.verse) state.featuredVerse = cue.verse;
  state.showHistory = [
    {
      id: cue.id,
      kind: cue.kind,
      eyebrow: cue.eyebrow || '',
      title: cue.title || '',
      body: String(cue.body || '').slice(0, 260),
      at: cue.at || new Date().toISOString(),
      source,
      simulated: Boolean(cue.simulated)
    },
    ...(state.showHistory || []).filter((entry) => entry.id !== cue.id)
  ].slice(0, 20);

  lastPublishedCue = cue;
  lastPublishedAt = Date.now();

  // Visual first: the overlay should never wait on speech synthesis.
  broadcastNotification('show.cue', { cue });
  broadcastNotification('show.state', { show: showPayload() });
  applySceneForCue(cue);
  saveState();

  const showSettings = state.settings.show || {};
  if (!state.settings.ttsEnabled || showSettings.narration === false || !cue.ttsText) return;
  // Welcome greetings queue behind whatever is speaking; the stage plays them
  // back one at a time. Other cues keep the original "still speaking" guard so
  // a prayer or verse is never stacked by the program's own timer.
  const isWelcomeCue = cue.kind === 'welcome';
  if (!isWelcomeCue && Date.now() < narrationBusyUntil) {
    console.log('[Show] Narration skipped: previous prayer is still speaking.');
    return;
  }
  try {
    const result = await ttsManager.synthesize(cue.ttsText, { lang: 'en' });
    if (!result.ok) {
      console.warn(`[Show] Narration unavailable: ${result.error}`);
      return;
    }
    inspectTtsAudio(result, `the ${cue.kind || 'show'} cue`);
    const durationSec = Math.max(2, Number(result.durationSec) || 8);
    // Leaves room for the client's fade-out and a natural pause afterwards.
    narrationBusyUntil = isWelcomeCue
      ? Math.max(narrationBusyUntil, Date.now() + durationSec * 1000 + 2200)
      : Date.now() + durationSec * 1000 + 2200;
    broadcastNotification('tts.play', {
      text: cue.ttsText,
      voice: result.voice,
      language: result.language,
      url: result.url,
      durationSec,
      source: 'show',
      welcome: isWelcomeCue
    });
  } catch (err) {
    console.warn('[Show] Narration failed:', err.message);
  }
}

function applyShowUpdate(params = {}) {
  const show = state.settings.show;
  if (typeof params.enabled === 'boolean') {
    show.enabled = params.enabled;
    if (params.enabled) show.paused = false;
  }
  if (typeof params.paused === 'boolean') show.paused = params.paused;
  if (typeof params.welcomeEnabled === 'boolean') show.welcomeEnabled = params.welcomeEnabled;
  if (typeof params.narration === 'boolean') show.narration = params.narration;
  if (params.pace !== undefined) show.pace = clampNumber(params.pace, 0.5, 1.5, show.pace);
  if (typeof params.theme === 'string') {
    const valid = params.theme === 'auto' || PRAYER_THEMES.some((theme) => theme.id === params.theme);
    if (valid) show.theme = params.theme;
  }
  showProgram?.sync();
  saveState();
  broadcastNotification('show.state', { show: showPayload() });
  broadcastNotification('temple.state', getPublicState());
  return showPayload();
}

// ============================================================================
// 10b. BIBLE QUIZ, GIFT EXPERIENCE, SCENE MATCHING
// ============================================================================
function quizPayload() {
  if (!quizEngine) {
    return {
      enabled: Boolean(state.settings.quiz && state.settings.quiz.enabled),
      frequencyMinutes: state.settings.quiz?.frequencyMinutes || 10,
      revealSeconds: state.settings.quiz?.revealSeconds || 25,
      tts: state.settings.quiz ? state.settings.quiz.tts !== false : true,
      totalQuestions: QUIZ_QUESTIONS.length,
      active: null
    };
  }
  const payload = quizEngine.status();
  payload.totalQuestions = QUIZ_QUESTIONS.length;
  return payload;
}

async function narrateQuizReveal(payload) {
  const quiz = state.settings.quiz || {};
  if (quiz.tts === false || !state.settings.ttsEnabled) return;
  if (Date.now() < narrationBusyUntil) {
    console.log('[Quiz] Narration skipped: another prayer is still speaking.');
    return;
  }
  const reference = String(payload.reference || '').replace(/\s*\(KJV\)\s*/i, '');
  const text = `The answer is ${payload.answer}. ${payload.explanation} ${reference}.`;
  try {
    const result = await ttsManager.synthesize(text, { lang: 'en' });
    if (!result.ok) {
      console.warn(`[Quiz] Narration unavailable: ${result.error}`);
      return;
    }
    inspectTtsAudio(result, 'the quiz answer');
    const durationSec = Math.max(2, Number(result.durationSec) || 8);
    narrationBusyUntil = Date.now() + durationSec * 1000 + 2200;
    broadcastNotification('tts.play', {
      text,
      voice: result.voice,
      language: result.language,
      url: result.url,
      durationSec,
      source: 'quiz'
    });
  } catch (err) {
    console.warn('[Quiz] Narration failed:', err.message);
  }
}

function publishQuizEvent(type, payload) {
  broadcastNotification(`quiz.${type}`, { ...payload, quiz: quizPayload() });
  if (type === 'reveal') narrateQuizReveal(payload).catch(() => {});
  saveState();
}

function applyQuizUpdate(params = {}) {
  const quiz = state.settings.quiz;
  if (typeof params.enabled === 'boolean') quiz.enabled = params.enabled;
  if (params.frequencyMinutes !== undefined) {
    quiz.frequencyMinutes = clampNumber(params.frequencyMinutes, 2, 120, quiz.frequencyMinutes);
  }
  if (params.revealSeconds !== undefined) {
    quiz.revealSeconds = clampNumber(params.revealSeconds, 10, 90, quiz.revealSeconds);
  }
  if (typeof params.tts === 'boolean') quiz.tts = params.tts;

  quizEngine.sync();
  if (quiz.enabled && !quizEngine.active) quizEngine.scheduleNext(30000);
  saveState();
  broadcastNotification('quiz.state', { quiz: quizPayload() });
  broadcastNotification('temple.state', getPublicState());
  return quizPayload();
}

function applyGiftUpdate(params = {}) {
  const gifts = state.settings.gifts;
  if (typeof params.announce === 'boolean') gifts.announce = params.announce;
  if (typeof params.tts === 'boolean') gifts.tts = params.tts;
  saveState();
  broadcastNotification('temple.state', getPublicState());
  return gifts;
}

function applyCongregationUpdate(params = {}) {
  const payload = congregation.configure(params);
  state.settings.congregation = { ...payload.settings };
  saveState();
  broadcastNotification('temple.state', getPublicState());
  return payload;
}

// ============================================================================
// 10c. SMART DAILY SCHEDULE (US timezones → programming mode)
// ============================================================================
let lastScheduleApply = null;

function schedulePayload() {
  if (!smartSchedule) {
    return { enabled: false, mode: 'disabled', current: null, programs: [], local: null };
  }
  return { ...smartSchedule.payload(), lastApplied: lastScheduleApply };
}

function eligibleStageImages() {
  return BACKGROUNDS.images.filter((image) => !broadcastSafeMode || image.copyright?.eligible);
}

/**
 * Background used when a programming mode starts.
 * Programs no longer prefer their own image categories: a missing current
 * image is replaced from the same global pool the rotation timer uses.
 */
function programBackgroundImage() {
  const pool = backgroundPool();
  if (pool.length === 0) return null;
  const current = pool.find((image) => image.url === state.settings.background.current);
  if (current) return { image: current, changed: false };
  const next = pool[Math.floor(Math.random() * pool.length)];
  return { image: next, changed: true };
}

/** Moves to a track whose category belongs to the program, never interrupting speech. */
function programMusicTrack(program) {
  const wanted = (program.musicCategories || []).map((category) => String(category).toLowerCase());
  if (wanted.length === 0) return null;
  const playable = playableMusicTracks();
  const current = playable.find((track) => track.id === state.settings.music.track);
  if (current && wanted.includes(String(current.category || '').toLowerCase())) {
    return { track: current, changed: false };
  }
  const match = playable.find((track) => wanted.includes(String(track.category || '').toLowerCase()))
    || playable[0];
  if (!match) return null;
  return { track: match, changed: match.id !== state.settings.music.track };
}

function buildProgramIntroCue(program) {
  if (!program) return null;
  const atmosphere = String(program.atmosphere || '').replace(/[.\s]+$/, '');
  const body = atmosphere
    ? `${atmosphere}. However this day finds you, you are welcome to pray with us.`
    : 'However this day finds you, you are welcome to pray with us.';
  return {
    id: `cue_${Date.now()}_program`,
    kind: 'welcome',
    eyebrow: 'PROGRAM',
    title: program.label,
    body: `Welcome to ${program.label}. ${body}`,
    note: 'Faith \u2022 Hope \u2022 Love',
    displayMs: 26000,
    ttsText: `Welcome to ${program.label}. ${body}`,
    at: new Date().toISOString()
  };
}

/**
 * Applies a programming mode to the existing show, quiz, music and stage engines.
 * It never restarts the TikTok connection, the show timer or playback.
 */
function applyProgramContent(program, { source = 'scheduled', announce = false, syncQuiz = true } = {}) {
  if (!program) return null;
  const applied = {
    id: program.id,
    label: program.label,
    source,
    at: new Date().toISOString()
  };

  // Prayer themes, verse tags and pacing for the shared show program.
  showProgram?.setProgramContext({
    id: program.id,
    label: program.label,
    prayerThemes: program.prayerThemes,
    verseTags: program.verseTags,
    narrationPace: program.narrationPace
  });
  // The program's theme list already narrows the prayer pool. Pinning a single
  // theme is only a fallback for a program that does not define any.
  state.settings.show.theme = (program.prayerThemes && program.prayerThemes.length > 0)
    ? 'auto'
    : (program.theme || 'auto');
  state.settings.show.pace = clampNumber(program.narrationPace, 0.5, 1.5, state.settings.show.pace);
  state.settings.show.welcomeEnabled = program.welcomeEnabled !== false;
  state.settings.quiz.frequencyMinutes = clampNumber(
    program.quizFrequencyMinutes,
    2,
    120,
    state.settings.quiz.frequencyMinutes
  );
  state.settings.gifts.announce = program.giftAnnounce !== false;
  state.settings.gifts.tts = program.giftTts !== false;
  // At boot the startup path schedules the first quiz itself (45 s); syncing here
  // would push that first question out by a full quiz interval.
  if (syncQuiz) quizEngine?.sync();

  // Background rotation stays global; a program never narrows the image pool.
  const background = programBackgroundImage();
  if (background) {
    configureBackgroundRotation();
    if (background.changed) {
      const image = setCurrentBackground(background.image.url);
      applied.background = image?.url || background.image.url;
      applied.backgroundChanged = true;
    } else {
      applied.background = background.image.url;
      applied.backgroundChanged = false;
    }
  }

  // Music category follows the program; ducking and volume stay untouched.
  const music = programMusicTrack(program);
  if (music) {
    applied.music = music.track.title;
    applied.musicChanged = music.changed;
    if (music.changed) applyMusicUpdate({ track: music.track.id });
  }

  saveState();
  lastScheduleApply = applied;
  broadcastNotification('show.state', { show: showPayload() });
  broadcastNotification('temple.state', getPublicState());

  if (announce) {
    const cue = buildProgramIntroCue(program);
    if (cue) {
      Promise.resolve(publishShowCue(cue, { source: 'schedule' })).catch((err) => {
        console.warn('[Schedule] Program intro failed:', err.message);
      });
    }
  }
  return applied;
}

function handleScheduleChange(program, previousId, meta = {}) {
  if (!program) {
    broadcastNotification('schedule.state', { schedule: schedulePayload() });
    return;
  }
  const announce = ['scheduled', 'override', 'override-expired'].includes(meta.reason);
  applyProgramContent(program, { source: meta.reason || 'scheduled', announce });
  if (meta.reason !== 'startup') {
    healthMonitor?.addIncident({
      component: 'schedule',
      severity: 'info',
      message: `Programming mode is now ${program.label}.`,
      action: `Applied ${program.prayerThemes?.length || 0} prayer themes and ${program.quizFrequencyMinutes || '—'} min quiz cadence.`,
      result: `Previous mode: ${previousId || 'none'}`
    });
  }
  broadcastNotification('schedule.state', {
    schedule: schedulePayload(),
    transition: { from: previousId || null, to: program.id, reason: meta.reason || 'scheduled' }
  });
}

/** Visual theme for each program cue, using only the locally stored categories. */
const SCENE_BY_THEME = {
  morning: 'backgrounds',
  healing: 'candles',
  family: 'church',
  anxiety: 'backgrounds',
  finances: 'church',
  strength: 'cross',
  night: 'candles',
  gratitude: 'bible'
};

function sceneCategoryForCue(cue) {
  if (!cue) return null;
  switch (cue.kind) {
    case 'welcome': return 'cathedral';
    case 'verse':
    case 'reflection': return 'bible';
    case 'community': return 'church';
    case 'gratitude': return 'bible';
    case 'prayer': return SCENE_BY_THEME[cue.theme] || 'cathedral';
    default: return null;
  }
}

function applySceneForCue(cue) {
  const background = state.settings.background;
  if (!background || background.sceneMatch === false) return;
  // Auto-rotation owns the stage and cycles every eligible image, so a
  // segment-specific scene must not narrow the visible library.
  if (background.enabled && backgroundPool().length > 1) return;
  const category = sceneCategoryForCue(cue);
  if (!category || !BACKGROUNDS.categories.includes(category)) return;
  const pool = BACKGROUNDS.images.filter(
    (image) => image.category === category
      && image.url !== background.current
      && (!broadcastSafeMode || image.copyright?.eligible)
  );
  if (pool.length === 0) {
    console.warn('[Copyright] No eligible background in scene category:', category);
    return;
  }
  const next = pool[Math.floor(Math.random() * pool.length)];
  // Recorded for the Admin grid; it never gates the rotation pool.
  background.category = category;
  setCurrentBackground(next.url, { rotate: true });
  configureBackgroundRotation();
}

let backgroundTimer = null;

/**
 * The single rotation pool: every broadcast-eligible image in the library,
 * across all seven categories. Program preferences, the scene-matching accent
 * and the Admin category filter never shrink it; Copyright Safe Mode still
 * decides what is eligible.
 */
function backgroundPool() {
  return eligibleStageImages();
}

function pickNextBackground() {
  const pool = backgroundPool();
  if (pool.length === 0) return null;
  const current = state.settings.background.current;
  const candidates = pool.filter((img) => img.url !== current);
  const source = candidates.length > 0 ? candidates : pool;
  if (state.settings.background.randomize) {
    return source[Math.floor(Math.random() * source.length)];
  }
  const currentIndex = pool.findIndex((img) => img.url === current);
  return pool[(currentIndex + 1) % pool.length];
}

function setCurrentBackground(url, { rotate = false } = {}) {
  const image = BACKGROUNDS.images.find((img) => img.url === url);
  if (!image) throw new Error('Background image not found');
  const decision = broadcastSafety.image(image.url, { safeMode: broadcastSafeMode });
  if (!decision.selectable) {
    console.warn('[Copyright] Blocked background:', image.url, decision.reason);
    throw new Error(`Copyright Safe Mode blocks that background: ${decision.reason}`);
  }
  state.settings.background.current = image.url;
  saveState();
  broadcastNotification('stage.background', {
    url: image.url,
    category: image.category,
    transitionMs: state.settings.background.transitionMs,
    source: rotate ? 'rotation' : 'manual',
    settings: state.settings.background
  });
  broadcastNotification('temple.state', getPublicState());
  return image;
}

function configureBackgroundRotation() {
  if (backgroundTimer) {
    clearInterval(backgroundTimer);
    backgroundTimer = null;
  }
  const bg = state.settings.background;
  if (!bg.enabled || backgroundPool().length < 2) return;
  const intervalMs = clampNumber(bg.intervalSeconds, 10, 3600, 60) * 1000;
  backgroundTimer = setInterval(() => {
    try {
      const next = pickNextBackground();
      if (next) setCurrentBackground(next.url, { rotate: true });
    } catch (err) {
      console.warn('[Background] Rotation failed:', err.message);
    }
  }, intervalMs);
}

// ============================================================================
// 10. VIEWER COMMENTS, COMMANDS AND PRAYER DETECTION
// ============================================================================
const COMMAND_KEYS = ['amen', 'pray', 'jesus', 'faith', 'hope', 'love', 'prayer', 'god'];
const commandCooldowns = new Map();
const GLOBAL_COMMAND_COOLDOWN_MS = 2500;
let lastCommandAt = 0;

function normaliseComment(text) {
  return String(text || '')
    .toLowerCase()
    .replace(/[’']/g, '')
    .replace(/[^a-z\s]/g, ' ')
    .replace(/\s+/g, ' ')
    .trim();
}

function detectCommand(rawText) {
  const norm = normaliseComment(rawText);
  if (!norm) return null;
  if (/\bthank\s*you\b/.test(norm)) return 'THANK YOU';
  for (const key of COMMAND_KEYS) {
    if (new RegExp(`\\b${key}\\b`).test(norm)) return key.toUpperCase();
  }
  return null;
}

function isPrayerRequestComment(rawText) {
  const lower = String(rawText || '').toLowerCase();
  return messageLibrary.triggers().some((trigger) => lower.includes(trigger));
}

function pushChatFeed(entry) {
  const text = baseClean(stripHtml(entry.text), 90);
  if (!text) return null;
  const item = {
    id: `chat_${Date.now()}_${Math.random().toString(36).slice(2, 5)}`,
    user: firstNameForDisplay(entry.user),
    text: isBlockedContent(text) ? '…' : text,
    avatar: entry.avatar || '',
    at: new Date().toISOString()
  };
  state.chatFeed.unshift(item);
  if (state.chatFeed.length > 8) state.chatFeed.length = 8;
  broadcastNotification('live.chat', { entry: item, chatFeed: chatFeedForList() });
  return item;
}

function chatFeedForList() {
  return state.chatFeed.map((item) => ({
    id: item.id,
    user: item.user,
    text: item.text,
    avatar: item.avatar || '',
    at: item.at
  }));
}

function handleCommand(command, { user, uniqueId, avatar, simulated = false, real = false }) {
  // AMEN glows on the viewer's congregation seat even while the spoken
  // acknowledgement is rate-limited. Only a real TikTok comment qualifies.
  if (command === 'AMEN' && real) {
    congregation.markAmen({ uniqueId, simulated });
  }

  const key = `${uniqueId || user}:${command}`;
  const now = Date.now();
  const last = commandCooldowns.get(key) || 0;
  if (now - last < 6000 || now - lastCommandAt < GLOBAL_COMMAND_COOLDOWN_MS) return null;
  commandCooldowns.set(key, now);
  lastCommandAt = now;
  if (commandCooldowns.size > 800) {
    commandCooldowns.delete(commandCooldowns.keys().next().value);
  }

  const message = messageLibrary.command(command);
  if (!message) return null;
  const member = recordMember(user, uniqueId, avatar, 1);
  if (command === 'AMEN') state.amenCount += 1;
  if (command === 'PRAY' || command === 'PRAYER') state.blessingsCount += 1;

  const event = pushEventLog({
    type: 'commentCommand',
    kind: 'command',
    command,
    user: member.name,
    uniqueId: member.uniqueId,
    avatar: member.avatar,
    message,
    simulated: Boolean(simulated),
    ttsText: state.settings.ttsEnabled ? message : '',
    ttsLang: 'en',
    merit: 1
  });

  saveState();
  broadcastNotification('temple.event', { event, state: getPublicState() });
  return event;
}

function handleViewerComment(commentText, user, uniqueId, avatar, options = {}) {
  const raw = String(commentText || '').trim();
  if (!raw || isBlockedContent(raw)) return null;

  if (options.source === 'tiktok') congregation.touch({ uniqueId });
  const memberName = sanitizeDisplayName(user || uniqueId);

  // Quiz answers are checked first so the correct answer is never printed in
  // the public chat feed before the reveal.
  if (quizEngine) {
    const answer = quizEngine.submitAnswer({ text: raw, name: memberName, uniqueId });
    if (answer?.correct) {
      pushChatFeed({ user: memberName, text: 'answered the Bible quiz', avatar });
      return { quizAnswer: true, already: answer.already, questionId: answer.question.id };
    }
  }

  pushChatFeed({ user: memberName, text: raw, avatar });

  // Prayer requests take priority: "pray for me" also contains the PRAY keyword.
  if (isPrayerRequestComment(raw)) {
    if (state.settings.prayer.interactionEnabled === false) {
      return { chat: true, prayerDisabled: true, member: recordMember(memberName, uniqueId, avatar, 0).name };
    }
    const request = addPrayerRequest({
      name: memberName,
      uniqueId,
      avatar,
      text: raw,
      source: options.source || 'tiktok'
    });
    return request || { skipped: true };
  }

  const command = detectCommand(raw);
  if (command) {
    // A real Amen comment updates the LIVE Activity row on every comment, even
    // when the spoken acknowledgement below is rate-limited.
    if (command === 'AMEN' && options.source === 'tiktok') {
      broadcastNotification('live.amen', {
        user: memberName,
        uniqueId,
        at: new Date().toISOString()
      });
    }
    const event = handleCommand(command, {
      user: memberName,
      uniqueId,
      avatar,
      simulated: options.source === 'simulation',
      real: options.source === 'tiktok'
    });
    return event || { skipped: true };
  }

  const member = recordMember(memberName, uniqueId, avatar, 0);
  return { chat: true, member: member.name };
}

// ============================================================================
// 11. TIKTOK LIVE CONNECTOR
// ============================================================================
let tiktokConn = null;
let tiktokConnectInFlight = false;
const tiktokRetry = {
  timer: null,
  attempts: 0,
  manualDisconnect: false,
  lastAttemptAt: null,
  nextRetryAt: null
};
// Connector errors that need a human, not another retry.
const TIKTOK_ATTENTION_RE = /(auth|login|captcha|verif|cookie|session|forbidden|unauthor|sign.?in|\b401\b|\b403\b)/i;

async function resolveTikTokUsername(rawInput) {
  let input = String(rawInput || '').trim();
  if (!input) throw new Error('Please enter a TikTok @username or Live link.');
  if (input.startsWith('http://') || input.startsWith('https://') || input.includes('tiktok.com/')) {
    const urlToFetch = input.startsWith('http') ? input : `https://${input}`;
    const directMatch = urlToFetch.match(/tiktok\.com\/@([^/?#]+)/i);
    if (directMatch && directMatch[1]) return directMatch[1];
    try {
      const resp = await fetch(urlToFetch, { redirect: 'follow' });
      const finalUrl = resp.url || '';
      const resolvedMatch = finalUrl.match(/tiktok\.com\/@([^/?#]+)/i);
      if (resolvedMatch && resolvedMatch[1]) return resolvedMatch[1];
    } catch (err) {
      console.warn('[TikTok URL Resolve]', err.message);
    }
  }
  return input.replace(/^@/, '').split(/[/?#]/)[0].trim();
}

function extractUserFromEvent(data) {
  const u = data?.user || data || {};
  const uniqueId = u.uniqueId || u.displayId || data?.uniqueId || '';
  const user = u.nickname || uniqueId || data?.nickname || 'Friend';
  const avatar =
    u.profilePictureUrl ||
    u.avatarLarge?.urlList?.[0] ||
    u.avatarThumb?.urlList?.[0] ||
    u.avatarMedium?.urlList?.[0] ||
    data?.profilePictureUrl ||
    '';
  return { user, uniqueId, avatar };
}

const giftComboTracker = new Map();

function formatConnectorError(err) {
  if (!err) return '';
  if (typeof err === 'string') return err.slice(0, 300);
  const direct = err.message || err.info || err.msg || err.code;
  if (direct) return String(direct).slice(0, 300);
  try {
    const json = JSON.stringify(err);
    if (json && json !== '{}') return json.slice(0, 300);
  } catch (_) {}
  return String(err).slice(0, 300);
}

function disposeTikTokConnection() {
  const stale = tiktokConn;
  tiktokConn = null;
  if (!stale) return;
  try {
    stale.removeAllListeners();
  } catch (_) {}
  try {
    const result = stale.disconnect();
    if (result && typeof result.catch === 'function') result.catch(() => {});
  } catch (_) {}
}

function tiktokPolicy() {
  const policy = state.settings.tiktok || {};
  return {
    autoReconnect: policy.autoReconnect !== false,
    maxRetries: clampNumber(policy.maxRetries, 0, 50, 6),
    retrySeconds: clampNumber(policy.retrySeconds, 5, 600, 10)
  };
}

function cancelTikTokReconnect(reason = '') {
  if (tiktokRetry.timer) {
    clearTimeout(tiktokRetry.timer);
    tiktokRetry.timer = null;
  }
  tiktokRetry.nextRetryAt = null;
  state.tiktok.nextRetryAt = null;
  if (reason) console.log(`[TikTok Live] Reconnect cancelled: ${reason}`);
}

/**
 * Exponential backoff. At most one timer exists, at most one connection is
 * created, and the configured @username is reused. Authentication problems stop
 * retrying and wait for an administrator instead of hammering the platform.
 */
function scheduleTikTokReconnect(reason, { immediate = false } = {}) {
  const policy = tiktokPolicy();
  if (tiktokRetry.manualDisconnect) return null;
  if (!policy.autoReconnect) {
    console.log('[TikTok Live] Auto reconnect is off; staying disconnected.');
    return null;
  }
  if (!state.tiktok.username) return null;
  if (state.tiktok.requiresAttention) return null;
  if (tiktokRetry.timer) return null;
  if (tiktokRetry.attempts >= policy.maxRetries) {
    state.tiktok.reconnecting = false;
    state.tiktok.requiresAttention = true;
    state.tiktok.lastDisconnectReason = reason;
    state.tiktok.nextRetryAt = null;
    broadcastNotification('temple.state', getPublicState());
    healthMonitor?.addIncident({
      component: 'tiktok',
      severity: 'error',
      message: `Could not reconnect to @${state.tiktok.username} after ${tiktokRetry.attempts} attempts.`,
      action: 'Automatic retries stopped',
      result: 'Use Retry Now after checking the account and LIVE status'
    });
    return null;
  }

  const delay = immediate
    ? 0
    : Math.min(300000, policy.retrySeconds * 1000 * Math.pow(2, tiktokRetry.attempts));
  tiktokRetry.attempts += 1;
  const nextAt = Date.now() + delay;
  tiktokRetry.nextRetryAt = nextAt;
  state.tiktok.reconnectAttempts = tiktokRetry.attempts;
  state.tiktok.reconnecting = true;
  state.tiktok.connecting = false;
  state.tiktok.nextRetryAt = new Date(nextAt).toISOString();
  state.tiktok.lastDisconnectReason = reason;
  broadcastNotification('temple.state', getPublicState());
  console.log(`[TikTok Live] Reconnect attempt ${tiktokRetry.attempts}/${policy.maxRetries} in ${Math.round(delay / 1000)}s (${reason})`);

  tiktokRetry.timer = setTimeout(async () => {
    tiktokRetry.timer = null;
    tiktokRetry.lastAttemptAt = new Date().toISOString();
    try {
      await connectTikTokLive(state.tiktok.username, { automatic: true });
    } catch (err) {
      console.warn('[TikTok Live] Reconnect failed:', err.message);
    }
  }, delay);
  if (typeof tiktokRetry.timer.unref === 'function') tiktokRetry.timer.unref();
  return { attempts: tiktokRetry.attempts, delay, nextAt: new Date(nextAt).toISOString() };
}

async function connectTikTokLive(usernameOrUrl, { automatic = false } = {}) {
  if (tiktokConnectInFlight) {
    console.log('[TikTok Live] A connection attempt is already running; ignoring the duplicate request.');
    return state.tiktok;
  }
  tiktokConnectInFlight = true;
  const cleanUser = await resolveTikTokUsername(usernameOrUrl || state.tiktok.username);
  if (!cleanUser) {
    tiktokConnectInFlight = false;
    throw new Error('Could not find a valid TikTok username in that input.');
  }

  if (!automatic) {
    tiktokRetry.manualDisconnect = false;
    tiktokRetry.attempts = 0;
    cancelTikTokReconnect();
  }
  cancelTikTokReconnect();
  disposeTikTokConnection();
  giftComboTracker.clear();

  state.tiktok = {
    ...state.tiktok,
    connected: false,
    connecting: true,
    reconnecting: Boolean(automatic),
    username: cleanUser,
    roomId: null,
    viewerCount: 0,
    lastError: null,
    connectStartedAt: new Date().toISOString(),
    reconnectAttempts: tiktokRetry.attempts,
    nextRetryAt: null,
    requiresAttention: false
  };
  broadcastNotification('temple.state', getPublicState());

  const connection = new TikTokLiveConnection(cleanUser, {
    processInitialData: true,
    fetchRoomInfoOnConnect: false,
    enableExtendedGiftInfo: false
  });
  tiktokConn = connection;

  connection.on(ControlEvent.CONNECTED, (roomState) => {
    if (tiktokConn !== connection) return;
    const reconnected = tiktokRetry.attempts > 0;
    state.tiktok.connected = true;
    state.tiktok.connecting = false;
    state.tiktok.reconnecting = false;
    state.tiktok.requiresAttention = false;
    state.tiktok.roomId = roomState?.roomId || connection.roomId || null;
    state.tiktok.lastError = null;
    state.tiktok.lastConnectedAt = new Date().toISOString();
    state.tiktok.connectStartedAt = null;
    state.tiktok.reconnectAttempts = 0;
    state.tiktok.nextRetryAt = null;
    tiktokRetry.attempts = 0;
    cancelTikTokReconnect();
    console.log(`[TikTok Live] Connected to @${cleanUser} (roomId: ${state.tiktok.roomId})`);
    broadcastNotification('temple.state', getPublicState());
    if (reconnected) {
      healthMonitor?.recordRecovery('tiktok', 'Automatic reconnect', 'Connected', {
        ok: true,
        message: `Reconnected to @${cleanUser}.`
      });
    }
  });

  connection.on(ControlEvent.DISCONNECTED, () => {
    if (tiktokConn !== connection) return;
    state.tiktok.connected = false;
    state.tiktok.connecting = false;
    state.tiktok.reconnecting = true;
    console.log(`[TikTok Live] Disconnected from @${cleanUser}`);
    broadcastNotification('temple.state', getPublicState());
    healthMonitor?.addIncident({
      component: 'tiktok',
      severity: 'warning',
      message: `TikTok Live connection to @${cleanUser} closed.`,
      action: 'Scheduling a reconnect with backoff',
      result: 'Awaiting retry'
    });
    scheduleTikTokReconnect('Connector reported a disconnect');
  });

  connection.on(ControlEvent.ERROR, (err) => {
    if (tiktokConn !== connection) return;
    const message = formatConnectorError(err);
    state.tiktok.lastError = message;
    state.tiktok.lastDisconnectReason = message;
    console.warn('[TikTok Live Warning]', message);
    if (TIKTOK_ATTENTION_RE.test(message)) {
      state.tiktok.requiresAttention = true;
      state.tiktok.reconnecting = false;
      cancelTikTokReconnect('authentication or access problem');
      healthMonitor?.addIncident({
        component: 'tiktok',
        severity: 'error',
        message: `TikTok Live needs attention: ${message}`,
        action: 'Automatic retries paused',
        result: 'Check the account, cookies and LIVE status, then use Retry Now'
      });
    }
    broadcastNotification('temple.state', getPublicState());
  });

  // Every decoded frame proves the socket is alive; no polling of the stream.
  connection.on(ControlEvent.RAW_DATA, () => {
    if (tiktokConn !== connection) return;
    state.tiktok.lastEventAt = new Date().toISOString();
  });

  connection.on(WebcastEvent.ROOM_USER, (data) => {
    const viewerCount = Number(data?.total ?? data?.viewerCount ?? 0);
    if (viewerCount > 0) {
      state.tiktok.viewerCount = viewerCount;
      broadcastNotification('temple.viewerCount', { viewerCount });
    }
  });

  connection.on(WebcastEvent.MEMBER, (data) => {
    const { user, uniqueId, avatar } = extractUserFromEvent(data);
    recordMember(user, uniqueId, avatar, 0);
    // One seat per uniqueId; duplicate MEMBER frames update the same viewer.
    // The connector has no leave event, so seats expire by inactivity only.
    const joined = congregation.join({ uniqueId, name: user, source: 'tiktok' });
    broadcastNotification('temple.state', getPublicState());
    // Real TikTok joins only. Simulation and test paths never reach this handler.
    if (joined.created) {
      showProgram?.welcome({ name: firstNameForDisplay(user), uniqueId }, 'tiktok');
    }
  });

  connection.on(WebcastEvent.CHAT, (data) => {
    const { user, uniqueId, avatar } = extractUserFromEvent(data);
    const commentText = data?.content || data?.comment || '';
    console.log(`[TikTok Chat] ${user}: ${commentText}`);
    handleViewerComment(commentText, user, uniqueId, avatar, { source: 'tiktok' });
  });

  connection.on(WebcastEvent.LIKE, (data) => {
    const { user, uniqueId, avatar } = extractUserFromEvent(data);
    congregation.touch({ uniqueId });
    const likeCount = clampNumber(data?.count ?? data?.likeCount, 1, 15, 1);
    state.likeCount += likeCount;
    Rituals.strikeWoodenFish({ user, uniqueId, avatar, count: likeCount });
  });

  connection.on(WebcastEvent.FOLLOW, (data) => {
    const { user, uniqueId, avatar } = extractUserFromEvent(data);
    congregation.touch({ uniqueId });
    state.followCount += 1;
    Rituals.ringBell({
      user,
      uniqueId,
      avatar,
      count: 1,
      kind: 'follow',
      message: messageLibrary.template('follow'),
      readTts: false
    });
  });

  connection.on(WebcastEvent.SHARE, (data) => {
    const { user, uniqueId, avatar } = extractUserFromEvent(data);
    congregation.touch({ uniqueId });
    state.shareCount += 1;
    Rituals.ringBell({
      user,
      uniqueId,
      avatar,
      count: 1,
      kind: 'share',
      message: messageLibrary.template('share'),
      readTts: false
    });
  });

  connection.on(WebcastEvent.SOCIAL, (data) => {
    const action = String(data?.action || '');
    const display = String(data?.common?.displayText?.displayType || data?.displayType || '').toLowerCase();
    const { user, uniqueId, avatar } = extractUserFromEvent(data);
    if (action === '3' || display.includes('follow')) {
      state.followCount += 1;
      Rituals.ringBell({
        user,
        uniqueId,
        avatar,
        kind: 'follow',
        message: messageLibrary.template('follow'),
        readTts: false
      });
    } else if (action === '1' || display.includes('share')) {
      state.shareCount += 1;
      Rituals.ringBell({
        user,
        uniqueId,
        avatar,
        kind: 'share',
        message: messageLibrary.template('share'),
        readTts: false
      });
    }
  });

  connection.on(WebcastEvent.STREAM_END, () => {
    // The LIVE session really ended: seats from that room are no longer live.
    console.log('[TikTok Live] Stream ended — clearing the prayer congregation.');
    congregation.reset('stream-ended');
    broadcastNotification('temple.state', getPublicState());
  });

  connection.on(WebcastEvent.GIFT, (data) => {
    const { user, uniqueId, avatar } = extractUserFromEvent(data);
    const giftObj = data?.gift || data?.giftDetails || {};
    const giftId = String(data?.giftId || giftObj?.id || 'gift');
    const groupId = String(data?.groupId || `${uniqueId}_${giftId}`);
    const repeatCount = Math.max(1, Number(data?.repeatCount || data?.comboCount || 1));

    const prevCount = giftComboTracker.get(groupId) || 0;
    if (repeatCount <= prevCount && data?.repeatEnd) {
      giftComboTracker.delete(groupId);
      return;
    }
    const deltaCount = Math.max(1, repeatCount - prevCount);
    giftComboTracker.set(groupId, repeatCount);
    if (giftComboTracker.size > 500) {
      giftComboTracker.delete(giftComboTracker.keys().next().value);
    }

    const diamondCount = Math.max(1, Number(giftObj?.diamondCount || data?.diamondCount || 1));
    const totalCoins = diamondCount * deltaCount;
    const rawGiftName = giftObj?.name || data?.giftName || 'a gift';
    const displayGiftName = deltaCount > 1 ? `${deltaCount}x ${rawGiftName}` : rawGiftName;

    console.log(`[TikTok Gift] ${user} sent ${displayGiftName} (${totalCoins} coins)`);
    Rituals.offerGift({
      user,
      uniqueId,
      avatar,
      coins: totalCoins,
      giftName: rawGiftName,
      quantity: deltaCount,
      source: 'tiktok'
    });
  });

  try {
    const roomState = await connection.connect();
    if (tiktokConn !== connection) return state.tiktok;
    state.tiktok.connected = true;
    state.tiktok.connecting = false;
    state.tiktok.reconnecting = false;
    state.tiktok.roomId = roomState?.roomId || connection.roomId || null;
    state.tiktok.lastConnectedAt = state.tiktok.lastConnectedAt || new Date().toISOString();
    state.tiktok.connectStartedAt = null;
    broadcastNotification('temple.state', getPublicState());
    return state.tiktok;
  } catch (err) {
    const message = formatConnectorError(err)
      || 'Could not connect to the Live room. Make sure the account is currently live.';
    state.tiktok.connected = false;
    state.tiktok.connecting = false;
    state.tiktok.lastError = message;
    state.tiktok.lastDisconnectReason = message;
    if (TIKTOK_ATTENTION_RE.test(message)) {
      state.tiktok.requiresAttention = true;
      state.tiktok.reconnecting = false;
      cancelTikTokReconnect('authentication or access problem');
      healthMonitor?.addIncident({
        component: 'tiktok',
        severity: 'error',
        message: `TikTok Live connection needs attention: ${message}`,
        action: 'Automatic retries paused',
        result: 'Administrator intervention required'
      });
    } else {
      scheduleTikTokReconnect(message);
    }
    broadcastNotification('temple.state', getPublicState());
    throw new Error(message);
  } finally {
    tiktokConnectInFlight = false;
  }
}

function disconnectTikTokLive({ manual = true } = {}) {
  if (manual) {
    tiktokRetry.manualDisconnect = true;
    cancelTikTokReconnect('administrator disconnected');
    tiktokRetry.attempts = 0;
  }
  disposeTikTokConnection();
  state.tiktok = {
    connected: false,
    connecting: false,
    reconnecting: false,
    username: '',
    roomId: null,
    viewerCount: 0,
    lastError: null,
    lastDisconnectReason: manual ? 'Disconnected by the administrator' : state.tiktok.lastDisconnectReason,
    lastConnectedAt: state.tiktok.lastConnectedAt,
    connectStartedAt: null,
    reconnectAttempts: 0,
    nextRetryAt: null,
    requiresAttention: false
  };
  congregation.reset('live-disconnected');
  broadcastNotification('temple.state', getPublicState());
  return state.tiktok;
}

/** Admin: change reconnect policy without touching the live connection. */
function applyTikTokReconnectSettings(params = {}) {
  const policy = state.settings.tiktok;
  if (typeof params.autoReconnect === 'boolean') policy.autoReconnect = params.autoReconnect;
  if (params.maxRetries !== undefined) policy.maxRetries = clampNumber(params.maxRetries, 0, 50, policy.maxRetries);
  if (params.retrySeconds !== undefined) policy.retrySeconds = clampNumber(params.retrySeconds, 5, 600, policy.retrySeconds);
  if (!policy.autoReconnect) cancelTikTokReconnect('auto reconnect disabled');
  saveState();
  broadcastNotification('temple.state', getPublicState());
  return { settings: policy, tiktok: state.tiktok };
}

function retryTikTokNow() {
  if (!state.tiktok.username) {
    throw new Error('No channel is configured. Connect a TikTok username first.');
  }
  if (tiktokConnectInFlight) {
    return { alreadyRunning: true, tiktok: state.tiktok };
  }
  cancelTikTokReconnect('manual retry');
  tiktokRetry.attempts = 0;
  state.tiktok.requiresAttention = false;
  tiktokRetry.manualDisconnect = false;
  const scheduled = scheduleTikTokReconnect('Manual retry requested', { immediate: true });
  return { scheduled, tiktok: state.tiktok };
}

/**
 * Detects a connector that claims to be connected while its socket is gone, and
 * a connect attempt that has hung. Both reset the connection once, then hand off
 * to the normal backoff retry. Nothing is inferred from a quiet chat.
 */
function checkTikTokStaleness() {
  if (!tiktokConn || tiktokRetry.manualDisconnect) return null;
  const connectedAt = state.tiktok.lastConnectedAt ? new Date(state.tiktok.lastConnectedAt).getTime() : 0;
  const gracePassed = connectedAt && Date.now() - connectedAt > 45000;
  const socket = tiktokConn._wsClientInstance;
  const socketClosed = socket && typeof socket.readyState === 'number' && socket.readyState !== 1;
  const reportsDisconnected = tiktokConn.isConnected === false;

  if (state.tiktok.connected && gracePassed && (socketClosed || reportsDisconnected)) {
    const reason = 'Connector socket is closed but the app still thought it was connected.';
    state.tiktok.connected = false;
    state.tiktok.reconnecting = true;
    state.tiktok.lastDisconnectReason = reason;
    console.warn(`[TikTok Live] Stale connection detected: ${reason}`);
    healthMonitor?.addIncident({
      component: 'tiktok',
      severity: 'warning',
      message: reason,
      action: 'Reconnecting with backoff',
      result: 'Connection reset'
    });
    disposeTikTokConnection();
    broadcastNotification('temple.state', getPublicState());
    scheduleTikTokReconnect(reason);
    return reason;
  }

  if (state.tiktok.connecting) {
    const startedAt = state.tiktok.connectStartedAt ? new Date(state.tiktok.connectStartedAt).getTime() : 0;
    if (startedAt && Date.now() - startedAt > 120000) {
      const reason = 'TikTok connect attempt timed out.';
      disposeTikTokConnection();
      state.tiktok.connecting = false;
      state.tiktok.lastDisconnectReason = reason;
      scheduleTikTokReconnect(reason);
      return reason;
    }
  }
  return null;
}

function startTikTokWatchdog() {
  if (tiktokWatchdog) return;
  tiktokWatchdog = setInterval(() => {
    try {
      checkTikTokStaleness();
    } catch (err) {
      console.warn('[TikTok Live] Watchdog error:', err.message);
    }
  }, 30000);
  if (typeof tiktokWatchdog.unref === 'function') tiktokWatchdog.unref();
}

// ============================================================================
// 12. DEMO AUTO-SIMULATION (optional, off by default)
// ============================================================================
let autoSimTimer = null;
const SIM_VIEWERS = [
  { user: 'Sarah M.', uniqueId: 'sarah.m', wish: 'Please pray for my family and for peace this week.' },
  { user: 'Michael R.', uniqueId: 'michael.r', wish: 'pray for my mother as she recovers at home' },
  { user: 'Grace L.', uniqueId: 'grace.l', wish: 'pray for me, I have an important interview tomorrow' },
  { user: 'David K.', uniqueId: 'david.k', wish: 'Please pray for my children and for wisdom.' },
  { user: 'Emily T.', uniqueId: 'emily.t', wish: 'pray for my family, we are going through a difficult season' },
  { user: 'James P.', uniqueId: 'james.p', wish: 'thank you for this prayer stream, it brings me peace' }
];

function runSingleSimulationStep() {
  const pick = SIM_VIEWERS[Math.floor(Math.random() * SIM_VIEWERS.length)];
  const roll = Math.random();
  if (roll < 0.3) {
    handleViewerComment(pick.wish, pick.user, pick.uniqueId, '', { source: 'simulation' });
  } else if (roll < 0.55) {
    Rituals.burnIncense({ user: pick.user, uniqueId: pick.uniqueId, count: 1, simulated: true });
  } else if (roll < 0.72) {
    Rituals.strikeWoodenFish({ user: pick.user, uniqueId: pick.uniqueId, count: 3, simulated: true });
  } else if (roll < 0.86) {
    handleViewerComment('AMEN', pick.user, pick.uniqueId, '', { source: 'simulation' });
  } else {
    Rituals.offerGift({
      user: pick.user,
      uniqueId: pick.uniqueId,
      coins: 12,
      giftName: 'Prayer candle',
      simulated: true
    });
  }
}

function configureAutoSim(enabled) {
  state.settings.autoSim = Boolean(enabled);
  if (autoSimTimer) {
    clearInterval(autoSimTimer);
    autoSimTimer = null;
  }
  if (state.settings.autoSim) {
    runSingleSimulationStep();
    autoSimTimer = setInterval(runSingleSimulationStep, state.settings.autoSimIntervalMs || 12000);
  }
}

// ============================================================================
// 13. JSON-RPC 2.0 DISPATCHER (legacy temple.* / live.* methods preserved)
// ============================================================================
async function handleRpcCall(method, params = {}) {
  switch (method) {
    // ---- State ----
    case 'temple.getState':
    case 'church.getState':
    case 'prayer.getState':
      return getPublicState();
    case 'state.get':
      return getPublicState();

    case 'engagement.status':
      return engagementStatusPayload();
    case 'engagement.test':
      return speakEngagementReminder(params.category || 'like', { manual: true });

    // ---- Legacy ritual methods ----
    case 'temple.burnIncense':
      return Rituals.burnIncense(params);
    case 'temple.strikeWoodenFish':
      return Rituals.strikeWoodenFish(params);
    case 'temple.ringBell':
      return Rituals.ringBell(params);
    case 'temple.sendPrayer':
      return Rituals.sendPrayer(params);
    case 'temple.offerGift':
      return Rituals.offerGift(params);
    case 'temple.drawFortune':
      return Rituals.drawFortune(params);
    case 'temple.grandCeremony':
      return Rituals.grandCeremony(params);
    case 'temple.updateSettings':
      return Rituals.updateSettings(params);
    case 'temple.resetMerit':
      return Rituals.resetMerit();
    case 'temple.comment':
      return handleViewerComment(params.comment, params.user, params.uniqueId, params.avatar, {
        source: params.source || 'rpc'
      });

    // ---- TTS ----
    case 'temple.speak': {
      const lang = params.lang || (params.voice === 'vi' ? 'vi' : 'auto');
      const res = await ttsManager.synthesize(params.text, {
        lang,
        voice: params.voice,
        rate: params.rate
      });
      if (res.ok && params.broadcast !== false) {
        broadcastNotification('tts.play', {
          text: params.text,
          voice: res.voice,
          language: res.language,
          url: res.url
        });
      }
      return res;
    }
    case 'temple.ttsStatus':
    case 'tts.status':
      return ttsManager.getStatus();
    case 'tts.voices':
      return {
        voices: VOICES,
        en: VOICES.filter((v) => v.language === 'en'),
        vi: VOICES.filter((v) => v.language === 'vi'),
        defaults: { en: state.settings.enVoice, vi: state.settings.vnVoice }
      };
    case 'tts.test': {
      const lang = params.lang === 'vi' ? 'vi' : 'en';
      const text = params.text || (lang === 'vi'
        ? 'Xin chào quý vị. Chúng ta hãy cùng nhau cầu nguyện.'
        : 'Welcome to Christian Prayer Live. Faith, hope and love.');
      const res = await ttsManager.synthesize(text, {
        lang,
        voice: params.voice || (lang === 'vi' ? state.settings.vnVoice : state.settings.enVoice),
        rate: params.rate
      });
      if (res.ok && params.broadcast !== false) {
        broadcastNotification('tts.play', {
          text,
          voice: res.voice,
          language: res.language,
          url: res.url
        });
      }
      return res;
    }

    // ---- Prayer request moderation ----
    case 'prayer.list':
      return { requests: publicPrayerRequests(), settings: state.settings.prayer };
    case 'prayer.add': {
      const request = addPrayerRequest({ ...params, source: params.source || 'admin' });
      if (!request) throw new Error('Prayer request was empty or blocked by the moderation filter.');
      return { request, requests: publicPrayerRequests(), state: getPublicState() };
    }
    case 'prayer.approve':
      return approvePrayerRequest(String(params.id || ''));
    case 'prayer.hide':
      return hidePrayerRequest(String(params.id || ''));
    case 'prayer.remove':
      return removePrayerRequest(String(params.id || ''));
    case 'prayer.clear':
      return clearPrayerRequests();
    case 'prayer.setPaused': {
      state.settings.prayer.paused = Boolean(params.paused);
      if (!state.settings.prayer.paused) {
        const waiting = state.prayerRequests.find(
          (req) => req.status === 'approved' && !req.displayedAt
        );
        if (waiting) displayPrayerRequest(waiting);
      }
      saveState();
      broadcastNotification('prayer.state', { requests: publicPrayerRequests(), state: getPublicState() });
      return { settings: state.settings.prayer, state: getPublicState() };
    }
    case 'prayer.setAutoApprove': {
      state.settings.prayer.autoApprove = Boolean(params.enabled);
      saveState();
      return { settings: state.settings.prayer, state: getPublicState() };
    }

    // ---- Backgrounds ----
    case 'stage.listBackgrounds':
      return {
        backgrounds: BACKGROUNDS.images,
        categories: BACKGROUNDS.categories,
        overlays: BACKGROUND_LAYER_FILES,
        settings: state.settings.background,
        safety: getBroadcastSafetyPayload()
      };
    case 'stage.setBackground': {
      const image = setCurrentBackground(String(params.url || params.path || ''));
      return { image, settings: state.settings.background };
    }
    case 'stage.nextBackground': {
      const next = pickNextBackground();
      if (!next) throw new Error('No background images available');
      const image = setCurrentBackground(next.url, { rotate: true });
      return { image, settings: state.settings.background };
    }
    case 'stage.updateSettings':
      return applySettingsUpdate({ background: params });

    // ---- Ambient worship music ----
    case 'music.get':
      return musicCatalogPayload();
    case 'music.update':
      return applyMusicUpdate(params);
    case 'music.next':
      return applyMusicUpdate({ track: pickAdjacentTrack(1) });
    case 'music.previous':
      return applyMusicUpdate({ track: pickAdjacentTrack(-1) });
    case 'music.toggle':
      return applyMusicUpdate({ paused: !state.settings.music.paused });
    case 'music.rescan': {
      const result = await MUSIC_LIBRARY.scan({ probe: true });
      applyMusicCatalog(result.catalog);
      const repaired = repairMusicSelection();
      if (repaired) saveState();
      const payload = musicRescanPayload(result);
      publishMusicLibrary(payload);
      if (repaired) broadcastNotification('music.state', { settings: state.settings.music });
      broadcastNotification('temple.state', getPublicState());
      return payload;
    }
    case 'music.track.update': {
      applyMusicCatalog(MUSIC_LIBRARY.updateTrack(params.id, params));
      const repaired = repairMusicSelection();
      saveState();
      const payload = musicCatalogPayload();
      publishMusicLibrary(payload);
      if (repaired) broadcastNotification('music.state', { settings: state.settings.music });
      return { ...payload, repaired };
    }
    case 'music.track.remove': {
      const { catalog, ...removal } = MUSIC_LIBRARY.removeTrack(params.id);
      applyMusicCatalog(catalog);
      const repaired = repairMusicSelection();
      saveState();
      const payload = { ...musicCatalogPayload(), removed: removal };
      publishMusicLibrary(payload);
      if (repaired) broadcastNotification('music.state', { settings: state.settings.music });
      broadcastNotification('temple.state', getPublicState());
      return payload;
    }

    // ---- Automated live show ----
    case 'show.status':
      return showPayload();
    case 'show.update':
      return applyShowUpdate(params);
    case 'show.next':
      return { cue: showProgram.nextSegment('manual'), show: showPayload() };
    case 'show.nextVerse':
      return { cue: showProgram.nextVerse('manual'), show: showPayload() };
    case 'show.nextReflection':
      return { cue: showProgram.nextReflection('manual'), show: showPayload() };
    case 'show.nextPrayer':
      return {
        cue: showProgram.nextPrayer('manual', params.theme && params.theme !== 'auto' ? params.theme : null),
        show: showPayload()
      };
    case 'show.testWelcome':
      return { cue: showProgram.testWelcome(params.name), show: showPayload() };
    case 'show.restart':
      return { cue: showProgram.restart({ source: 'manual' }), show: showPayload() };
    case 'show.farewell':
      return triggerFarewell(params);
    case 'show.farewellList':
      return farewellLibraryPayload();

    // ---- Bible quiz ----
    case 'quiz.status':
      return quizPayload();
    case 'quiz.update':
      return applyQuizUpdate(params);
    case 'quiz.next':
      return {
        quiz: quizEngine.next({ source: params.source === 'test' ? 'test' : 'manual' }),
        active: quizPayload().active
      };
    case 'quiz.reveal':
      return { quiz: quizEngine.reveal(), active: quizPayload().active };
    case 'quiz.answer':
      return {
        result: quizEngine.submitAnswer({
          text: params.text,
          name: params.name || 'Test Viewer (demo)',
          uniqueId: params.uniqueId || 'test.quiz'
        }),
        quiz: quizPayload()
      };

    // ---- Gift announcements ----
    case 'gift.update':
      return applyGiftUpdate(params);

    // ---- Copyright & licensing audit (fixed directories only) ----
    case 'copyright.get':
      return copyrightAudit.summary();
    case 'copyright.safety':
      return getBroadcastSafetyPayload();
    case 'copyright.setSafeMode':
      return applyCopyrightSafeMode(params.enabled !== false);
    case 'copyright.scan': {
      const result = await copyrightAudit.scan();
      const safety = refreshBroadcastMedia();
      broadcastNotification('copyright.updated', {
        generatedAt: result.generatedAt,
        counts: result.counts,
        changes: result.changes,
        safety
      });
      broadcastNotification('temple.state', getPublicState());
      return { ...result, safety };
    }

    // ---- Christian image library (fixed category folders only) ----
    case 'images.state':
      return enrichImageLibrary(imageLibrary.summary());
    case 'images.scan': {
      const scan = await imageLibrary.scan();
      // Rebuild the licensing inventory from the refreshed asset manifest so
      // the background catalog uses the same source of truth as the audit.
      const audit = await copyrightAudit.scan();
      const catalog = reloadBackgroundCatalog();
      const payload = enrichImageLibrary(scan);
      broadcastNotification('images.updated', {
        scannedAt: payload.scannedAt,
        totals: payload.totals,
        categories: payload.categories,
        changes: {
          added: payload.added,
          removed: payload.removed,
          renamed: payload.renamed,
          updated: payload.updated
        },
        catalog,
        copyright: { generatedAt: audit.generatedAt, counts: audit.counts, changes: audit.changes }
      });
      broadcastNotification('copyright.updated', {
        generatedAt: audit.generatedAt,
        counts: audit.counts,
        changes: audit.changes,
        safety: getBroadcastSafetyPayload()
      });
      broadcastNotification('temple.state', getPublicState());
      return { ...payload, catalog, copyright: { generatedAt: audit.generatedAt, counts: audit.counts, changes: audit.changes } };
    }

    // ---- Prayer congregation (live-session only, never persisted) ----
    case 'congregation.get':
      return congregation.getPayload();
    case 'congregation.update':
      return applyCongregationUpdate(params);
    case 'congregation.reset': {
      const result = congregation.reset('admin-reset');
      broadcastNotification('temple.state', getPublicState());
      return result;
    }
    case 'congregation.demo': {
      const result = congregation.additiveDemo(params.count);
      broadcastNotification('temple.state', getPublicState());
      return result;
    }
    case 'congregation.demoClear': {
      const result = congregation.clearDemo();
      broadcastNotification('temple.state', getPublicState());
      return result;
    }
    case 'congregation.demoEvent': {
      const result = congregation.demoAction(params);
      broadcastNotification('temple.state', getPublicState());
      return result;
    }

    // ---- Message library ----
    case 'messages.get':
      return messageLibrary.snapshot();
    case 'messages.save':
      return { saved: true, messages: messageLibrary.replace(params.messages || params) };

    // ---- Smart daily schedule (US timezones) ----
    case 'schedule.get':
      return schedulePayload();
    case 'schedule.update': {
      if (!smartSchedule) throw new Error('The smart schedule is not available.');
      smartSchedule.update({ enabled: params.enabled, timezone: params.timezone });
      smartSchedule.tick();
      broadcastNotification('schedule.state', { schedule: schedulePayload() });
      broadcastNotification('temple.state', getPublicState());
      return schedulePayload();
    }
    case 'schedule.program.update': {
      if (!smartSchedule) throw new Error('The smart schedule is not available.');
      const programId = String(params.id || params.program || '');
      smartSchedule.updateProgram(programId, params);
      const active = smartSchedule.current().program;
      if (active && active.id === programId) {
        applyProgramContent(active, { source: 'program-edit' });
      }
      broadcastNotification('schedule.state', { schedule: schedulePayload() });
      return schedulePayload();
    }
    case 'schedule.override': {
      if (!smartSchedule) throw new Error('The smart schedule is not available.');
      smartSchedule.setOverride(
        String(params.program || params.programId || ''),
        params.minutes !== undefined ? params.minutes : 30
      );
      smartSchedule.tick();
      broadcastNotification('schedule.state', { schedule: schedulePayload() });
      return schedulePayload();
    }
    case 'schedule.auto': {
      if (!smartSchedule) throw new Error('The smart schedule is not available.');
      const hadOverride = Boolean(smartSchedule.activeOverride());
      smartSchedule.clearOverride();
      smartSchedule.tick();
      if (!hadOverride) {
        const active = smartSchedule.current().program;
        if (active) applyProgramContent(active, { source: 'auto-return' });
      }
      broadcastNotification('schedule.state', { schedule: schedulePayload() });
      return schedulePayload();
    }
    case 'schedule.preview': {
      if (!smartSchedule) throw new Error('The smart schedule is not available.');
      const program = smartSchedule.programById(String(params.program || params.programId || ''));
      if (!program) throw new Error('Unknown program. Choose morning, afternoon, evening or night.');
      const applied = applyProgramContent(program, { source: 'preview', announce: false });
      return {
        preview: true,
        applied,
        schedule: schedulePayload(),
        note: 'Preview applied. Automatic switching continues and the scheduled mode is restored at the next transition or with Return to automatic.'
      };
    }
    case 'schedule.test':
      if (!smartSchedule) throw new Error('The smart schedule is not available.');
      return smartSchedule.debug(params.at ? Number(params.at) : undefined);

    // ---- System health & auto recovery ----
    case 'health.get':
      if (!healthMonitor) throw new Error('The health monitor is not running.');
      return healthMonitor.payload();
    case 'health.check': {
      if (!healthMonitor) throw new Error('The health monitor is not running.');
      const payload = healthMonitor.runCheck({ reason: params.reason || 'manual' });
      broadcastNotification('health.state', { health: payload });
      return payload;
    }
    case 'health.retry': {
      if (!healthMonitor) throw new Error('The health monitor is not running.');
      const component = String(params.component || '').toLowerCase();
      let action = null;
      if (['piper', 'tts', 'narration'].includes(component)) {
        action = ttsManager.recover({ manual: true });
        healthMonitor.recordRecovery('piper', 'Manual restart', 'Worker starting', {
          ok: true,
          message: 'Manual Piper restart requested from the dashboard.'
        });
      } else if (['tiktok', 'live'].includes(component)) {
        action = retryTikTokNow();
        healthMonitor.recordRecovery('tiktok', 'Manual reconnect', 'Retry scheduled', {
          ok: true,
          message: 'Manual TikTok reconnect requested from the dashboard.'
        });
      } else if (['music', 'audio', 'music-player'].includes(component)) {
        broadcastNotification('audio.recover', {
          reason: 'manual',
          trackId: state.settings.music.track,
          at: new Date().toISOString()
        });
        healthMonitor.recordRecovery('audio', 'Manual audio recovery', 'Stage asked to reload the track', {
          ok: true,
          message: 'Manual audio recovery requested.'
        });
        action = { requested: true };
      } else if (['music-files', 'files', 'musicfiles'].includes(component)) {
        const report = MUSIC_INTEGRITY.scan();
        healthMonitor.recordRecovery('music-files', 'Music integrity scan', report.summary, {
          ok: report.healthy,
          message: 'Music file integrity scan completed.'
        });
        action = report;
      } else {
        throw new Error(`Unknown component: ${component}. Use piper, tiktok, music or music-files.`);
      }
      const payload = healthMonitor.runCheck({ reason: `retry ${component}` });
      broadcastNotification('health.state', { health: payload });
      return { component, action, health: payload };
    }
    case 'health.alerts.clear': {
      if (!healthMonitor) throw new Error('The health monitor is not running.');
      const cleared = healthMonitor.clearResolved();
      const health = healthMonitor.payload();
      broadcastNotification('health.state', { health });
      return { ...cleared, health };
    }
    case 'health.export':
      if (!healthMonitor) throw new Error('The health monitor is not running.');
      return healthMonitor.exportReport();
    case 'health.audio': {
      if (!healthMonitor) throw new Error('The health monitor is not running.');
      const report = params.report && typeof params.report === 'object' ? params.report : params;
      const audio = healthMonitor.recordAudioReport({
        playing: Boolean(report.playing),
        paused: Boolean(report.paused),
        enabled: report.enabled !== false,
        muted: Boolean(report.muted),
        unlocked: report.unlocked !== false,
        ttsPlaying: Boolean(report.ttsPlaying),
        // null means "not measured" — it must not be mistaken for silence.
        musicRms: Number.isFinite(Number(report.musicRms)) ? Number(report.musicRms) : null,
        volume: Number(report.volume) || 0,
        trackId: report.trackId ? String(report.trackId).slice(0, 80) : null
      });
      return { ok: true, audio };
    }

    // ---- Music file integrity (read-only scans) ----
    case 'music.integrity': {
      const report = MUSIC_INTEGRITY.scan();
      broadcastNotification('music.integrity.updated', { report });
      return report;
    }
    case 'music.integrity.refresh': {
      const result = await MUSIC_LIBRARY.scan({ probe: true });
      applyMusicCatalog(result.catalog);
      const repaired = repairMusicSelection();
      if (repaired) saveState();
      const scan = musicRescanPayload(result).scan;
      const report = MUSIC_INTEGRITY.scan();
      publishMusicLibrary(musicCatalogPayload());
      broadcastNotification('music.integrity.updated', { report });
      broadcastNotification('temple.state', getPublicState());
      return { scan, report, track: state.settings.music.track, repaired };
    }

    // ---- TikTok Live ----
    case 'live.connect':
      return connectTikTokLive(params.username);
    case 'live.disconnect':
      return disconnectTikTokLive();
    case 'live.status':
      return {
        ...state.tiktok,
        settings: tiktokPolicy(),
        nextAttemptInSeconds: state.tiktok.nextRetryAt
          ? Math.max(0, Math.round((new Date(state.tiktok.nextRetryAt).getTime() - Date.now()) / 1000))
          : null
      };
    case 'live.setReconnect':
      return applyTikTokReconnectSettings(params);
    case 'live.retryNow':
      return { ...retryTikTokNow(), status: state.tiktok };
    case 'live.setAutoSim':
      configureAutoSim(Boolean(params.enabled));
      saveState();
      broadcastNotification('temple.state', getPublicState());
      return getPublicState();

    default:
      throw new Error(`Unknown JSON-RPC method: ${method}`);
  }
}

// ============================================================================
// 14. EXPRESS + WEBSOCKET SERVER
// ============================================================================
const app = express();
app.use(cors());
app.use(express.json({ limit: '2mb' }));
app.use('/tts-cache', express.static(TTS_CACHE_DIR, { maxAge: '7d' }));
app.use(express.static(PUBLIC_DIR, {
  etag: true,
  maxAge: 0,
  setHeaders: (res, filePath) => {
    if (/\.(html|css|js|json)$/i.test(filePath)) {
      res.setHeader('Cache-Control', 'no-cache, no-store, must-revalidate');
    }
  }
}));

app.get('/admin', (_req, res) => {
  res.sendFile(path.join(PUBLIC_DIR, 'admin.html'));
});

app.post('/rpc', async (req, res) => {
  const { jsonrpc, id, method, params } = req.body || {};
  if (!method) {
    return res.status(400).json({
      jsonrpc: '2.0',
      id: id ?? null,
      error: { code: -32600, message: 'Invalid JSON-RPC request: missing method' }
    });
  }
  try {
    const result = await handleRpcCall(method, params || {});
    res.json({ jsonrpc: jsonrpc || '2.0', id: id ?? null, result });
  } catch (err) {
    res.status(200).json({
      jsonrpc: jsonrpc || '2.0',
      id: id ?? null,
      error: { code: -32000, message: err.message || 'Server error' }
    });
  }
});

app.all('/api/tts', async (req, res) => {
  const text = String(req.body?.text || req.query?.text || '').trim();
  if (!text) return res.status(400).json({ ok: false, error: 'Missing text to speak' });
  const requestedVoice = String(req.body?.voice || req.query?.voice || '').trim();
  const lang = req.body?.lang || req.query?.lang
    || (requestedVoice === 'vi' ? 'vi' : 'auto');
  const rate = req.body?.rate || req.query?.rate || state.settings.ttsRate;
  const result = await ttsManager.synthesize(text, {
    lang,
    voice: requestedVoice === 'maichi' ? undefined : requestedVoice,
    rate
  });
  res.json(result);
});

app.get('/api/state', (_req, res) => res.json(getPublicState()));
app.get('/api/backgrounds', (_req, res) => res.json({
  backgrounds: BACKGROUNDS.images,
  categories: BACKGROUNDS.categories,
  overlays: BACKGROUND_LAYER_FILES,
  settings: state.settings.background,
  safety: getBroadcastSafetyPayload()
}));
app.get('/api/messages', (_req, res) => res.json(messageLibrary.snapshot()));
app.get('/api/music', (_req, res) => res.json(musicCatalogPayload()));
app.get('/api/copyright', (_req, res) => res.json(copyrightAudit.summary()));
app.get('/api/health', (_req, res) => res.json({
  ok: true,
  brand: BRAND,
  tts: ttsManager.getStatus(),
  tiktok: state.tiktok,
  backgrounds: BACKGROUNDS.images.length,
  eligibleBackgrounds: BACKGROUNDS.images.filter((img) => img.copyright?.eligible).length,
  musicTracks: MUSIC.tracks.length,
  musicLibrary: MUSIC.libraryMeta,
  copyrightSafeMode: broadcastSafeMode,
  broadcastSafety: getBroadcastSafetyPayload().counts,
  music: state.settings.music,
  congregation: congregation.getPayload().counts,
  schedule: smartSchedule ? {
    enabled: smartSchedule.config.enabled,
    timezone: smartSchedule.config.timezone,
    program: smartSchedule.current().program?.id || null,
    mode: smartSchedule.current().mode
  } : null,
  tiktokReconnect: tiktokPolicy(),
  musicIntegrity: MUSIC_INTEGRITY.summary(),
  health: healthMonitor ? {
    metrics: healthMonitor.payload().metrics,
    statuses: healthMonitor.componentStatuses(healthSnapshot()),
    counters: healthMonitor.counters,
    lastError: healthMonitor.lastError,
    lastRecovery: healthMonitor.lastRecovery
  } : null
}));

app.get('/api/diagnostics', (_req, res) => {
  if (!healthMonitor) return res.status(503).json({ ok: false, error: 'Health monitor is not running.' });
  res.setHeader('Cache-Control', 'no-store');
  res.json(healthMonitor.exportReport());
});

const server = http.createServer(app);
const wss = new WebSocketServer({ server, path: '/ws' });

function broadcastNotification(method, params) {
  const payload = JSON.stringify({ jsonrpc: '2.0', method, params });
  for (const client of wss.clients) {
    if (client.readyState === 1) client.send(payload);
  }
}

function wsClientCounts() {
  let total = 0;
  let obs = 0;
  for (const client of wss.clients) {
    total += 1;
    if (client.isObs) obs += 1;
  }
  return { total, obs, stage: obs };
}

/** Evidence the health monitor can use without reaching into module internals. */
function healthSnapshot() {
  return {
    tts: ttsManager ? { ...ttsManager.getHealth(), enabled: Boolean(state.settings.ttsEnabled) } : { status: 'starting' },
    tiktok: { ...state.tiktok, roomId: state.tiktok.roomId || null },
    music: { ...state.settings.music },
    musicIntegrity: MUSIC_INTEGRITY.report(),
    clients: wsClientCounts(),
    ttsQueue: ttsManager ? ttsManager.pending.size : 0,
    schedule: smartSchedule ? schedulePayload() : null
  };
}

wss.on('connection', (ws, req) => {
  try {
    const url = new URL(req?.url || '/ws', 'http://localhost');
    ws.isObs = url.searchParams.get('obs') === '1';
  } catch (_) {
    ws.isObs = false;
  }
  ws.send(JSON.stringify({ jsonrpc: '2.0', method: 'temple.state', params: getPublicState() }));
  ws.send(JSON.stringify({ jsonrpc: '2.0', method: 'show.state', params: { show: showPayload() } }));
  ws.send(JSON.stringify({ jsonrpc: '2.0', method: 'quiz.state', params: { quiz: quizPayload() } }));
  ws.send(JSON.stringify({ jsonrpc: '2.0', method: 'schedule.state', params: { schedule: schedulePayload() } }));
  if (healthMonitor) {
    ws.send(JSON.stringify({ jsonrpc: '2.0', method: 'health.state', params: { health: healthMonitor.payload() } }));
  }
  // Replay a cue that is still on screen so OBS can reload mid-prayer.
  if (lastPublishedCue) {
    const age = Date.now() - lastPublishedAt;
    if (age >= 0 && age < (Number(lastPublishedCue.displayMs) || 15000)) {
      ws.send(JSON.stringify({
        jsonrpc: '2.0',
        method: 'show.cue',
        params: { cue: lastPublishedCue, replay: true }
      }));
    }
  }
  if (state.settings.background.current) {
    ws.send(JSON.stringify({
      jsonrpc: '2.0',
      method: 'stage.background',
      params: {
        url: state.settings.background.current,
        transitionMs: 0,
        settings: state.settings.background
      }
    }));
  }

  ws.on('message', async (raw) => {
    let msg;
    try {
      msg = JSON.parse(raw.toString('utf8'));
    } catch (_) {
      return;
    }
    if (!msg || !msg.method) return;
    try {
      const result = await handleRpcCall(msg.method, msg.params || {});
      if (msg.id !== undefined) {
        ws.send(JSON.stringify({ jsonrpc: '2.0', id: msg.id, result }));
      }
    } catch (err) {
      if (msg.id !== undefined) {
        ws.send(JSON.stringify({
          jsonrpc: '2.0',
          id: msg.id,
          error: { code: -32000, message: err.message || 'RPC error' }
        }));
      }
    }
  });
});

ttsManager = new PiperManager();

engagementMessages = new EngagementMessages({
  getVerses: () => messageLibrary.data.bibleVerses || []
});
engagementScheduler = new EngagementScheduler({
  getSettings: () => state.settings.engagement || ENGAGEMENT_DEFAULTS,
  canSpeak: engagementAudiencePresent,
  speak: (category) => speakEngagementReminder(category),
  log: (message) => console.log(message)
});

quizEngine = new QuizEngine({
  getSettings: () => state.settings.quiz,
  recent: state.quizRecent,
  publish: publishQuizEvent,
  onChange: () => {
    if (!quizEngine) return;
    state.quizRecent = quizEngine.recent.slice(0, 50);
    saveState();
    broadcastNotification('quiz.state', { quiz: quizPayload() });
  }
});

showProgram = new ShowProgram({
  getSettings: () => state.settings.show,
  getVerses: () => messageLibrary.data.bibleVerses || [],
  getApprovedPrayers: () => state.prayerRequests
    .filter((request) => request.status === 'approved' && request.source !== 'simulation')
    .map((request) => ({ name: request.displayName, text: request.text })),
  publish: publishShowCue,
  onChange: () => {
    saveState();
    broadcastNotification('show.state', { show: showPayload() });
  }
});

// ---- Health, incidents and auto-recovery ------------------------------------
healthMonitor = new HealthMonitor({
  root: __dirname,
  dataDir: DATA_DIR,
  stateFile: HEALTH_STATE_FILE,
  getSnapshot: healthSnapshot,
  broadcast: (method, params) => broadcastNotification(method, params)
});
// Piper reports its own crash/restart cycle without knowing about the dashboard.
// Recovery events increment the counters; failures record a failed recovery.
ttsManager.onIncident = (incident) => {
  if (!healthMonitor) return;
  if (incident.recoveryFailed) {
    healthMonitor.recordRecovery('piper', incident.action, incident.result, {
      ok: false,
      message: incident.message
    });
    return;
  }
  if (incident.recovery) {
    healthMonitor.recordRecovery('piper', incident.action, incident.result, {
      ok: true,
      message: incident.message
    });
    return;
  }
  healthMonitor.addIncident(incident);
};

// ---- Smart daily schedule ---------------------------------------------------
smartSchedule = new SmartSchedule({
  filePath: SCHEDULE_FILE,
  backupPath: path.join(__dirname, 'config', 'schedule.backup.json'),
  onChange: handleScheduleChange
});

/**
 * Applies the programming mode for the current wall clock once at boot, then
 * keeps evaluating. Priming the signature keeps a restart from announcing the
 * same program a second time.
 */
function startSmartSchedule() {
  if (!smartSchedule) return;
  const initial = smartSchedule.current();
  if (smartSchedule.config.enabled && initial.program) {
    smartSchedule.appliedId = initial.program.id;
    smartSchedule.appliedSource = initial.override ? 'override' : 'scheduled';
    smartSchedule.appliedSignature = `${initial.program.id}:${smartSchedule.appliedSource}:${initial.override?.until || ''}`;
    applyProgramContent(initial.program, { source: 'startup', syncQuiz: false });
    console.log(`[Schedule] ${initial.program.label} — ${initial.parts.clock12} ${initial.parts.offsetLabel || ''} (${smartSchedule.config.timezone})`);
  } else {
    console.log('[Schedule] Smart schedule is disabled. Manual show controls remain in use.');
  }
  smartSchedule.start();
}

/** Waits briefly for Piper so the opening welcome cue is actually spoken. */
function startAutomatedShow() {
  if (!state.settings.show.enabled || state.settings.show.paused) {
    console.log('[Show] Automated program is off. Use the admin dashboard to start it.');
    return;
  }
  let attempts = 0;
  const begin = () => {
    if (ttsManager.ready || attempts >= 20) {
      showProgram.start({ immediate: true });
      console.log('[Show] Automated program started — welcome, Scripture, prayer, community, gratitude.');
      return;
    }
    attempts += 1;
    setTimeout(begin, 800);
  };
  begin();
}

server.listen(PORT, () => {
  const bgCount = BACKGROUNDS.images.length;
  console.log('============================================================');
  console.log('✝  CHRISTIAN PRAYER LIVE — Faith • Hope • Love');
  console.log('   "Pray Together. Grow in Faith."');
  console.log('------------------------------------------------------------');
  console.log(`📺 Livestream / OBS 9:16 : http://localhost:${PORT}`);
  console.log(`🎛️  Admin dashboard      : http://localhost:${PORT}/admin`);
  console.log(`🔌 JSON-RPC 2.0         : http://localhost:${PORT}/rpc (ws://localhost:${PORT}/ws)`);
  console.log(`🎨 Backgrounds          : ${bgCount} local images (rotation ${state.settings.background.enabled ? 'on' : 'off'})`);
  console.log(`🗣️  Piper voices         : EN ${state.settings.enVoice} | VI ${state.settings.vnVoice}`);
  console.log(`🪑 Prayer congregation   : ${state.settings.congregation.maxVisible} seats · names ${state.settings.congregation.showNames ? 'on' : 'off'} · inactivity ${state.settings.congregation.inactivityMinutes}m`);
  const scheduled = smartSchedule ? smartSchedule.current() : null;
  if (scheduled?.program) {
    console.log(`🕒 Smart schedule        : ${scheduled.program.label} · ${scheduled.parts.clock12} ${scheduled.parts.offsetLabel} (${smartSchedule.config.timezone})`);
  }
  console.log('============================================================');

  // Music integrity is read-only: it never deletes or rewrites audio.
  try {
    const integrity = MUSIC_INTEGRITY.scan();
    console.log(`[Music] Integrity: ${integrity.summary} (${integrity.totalFilesOnDisk} files on disk)`);
    if (!integrity.healthy) {
      healthMonitor?.addIncident({
        component: 'music-files',
        severity: 'warning',
        message: `Music integrity: ${integrity.summary}`,
        action: 'Startup scan',
        result: 'Review the missing files list in the dashboard'
      });
    }
  } catch (err) {
    console.warn('[Music] Integrity scan failed:', err.message);
  }

  // Pick up audio files added or removed while the server was stopped.
  MUSIC_LIBRARY.scan({ probe: false }).then((result) => {
    applyMusicCatalog(result.catalog);
    const repaired = repairMusicSelection();
    if (repaired) saveState();
    if (result.addedCount || result.removedCount) {
      console.log(`[Music] Library sync: ${result.found} tracks, ${result.addedCount} new, ${result.removedCount} missing.`);
      if (repaired) broadcastNotification('music.state', { settings: state.settings.music });
    }
  }).catch((err) => console.warn(`[Music] Startup library sync failed: ${err.message}`));

  configureBackgroundRotation();
  if (state.settings.autoSim) configureAutoSim(true);
  startSmartSchedule();
  healthMonitor.start();
  startTikTokWatchdog();
  startAutomatedShow();
  if (state.settings.engagement?.enabled !== false) {
    engagementScheduler.start();
    console.log('[Engagement] Reminders on — like 120s · share 240s · gift 360s · prayer 480s · Scripture 600s.');
  } else {
    console.log('[Engagement] Reminders are off. Enable them from the dashboard.');
  }
  if (state.settings.quiz.enabled) {
    quizEngine.sync({ firstRun: true });
    console.log('[Quiz] Bible quiz enabled — first question in about 45 seconds.');
  } else {
    console.log('[Quiz] Bible quiz is off. Enable it from the dashboard.');
  }

  const defaultChannel = CONFIG.tiktok.autoConnect ? (CONFIG.tiktok.username || '') : '';
  if (defaultChannel) {
    connectTikTokLive(defaultChannel).catch((err) => {
      console.warn(`[Auto-Connect @${defaultChannel}]`, err.message);
    });
  } else {
    console.log('[TikTok Live] No channel configured. Connect from the admin dashboard when you are live.');
  }
});

process.on('SIGINT', () => {
  console.log('\n[Server] Shutting down...');
  try {
    if (showProgram) showProgram.stop();
  } catch (_) {}
  try {
    if (engagementScheduler) engagementScheduler.stop();
  } catch (_) {}
  try {
    if (quizEngine) quizEngine.stop();
  } catch (_) {}
  try {
    if (smartSchedule) smartSchedule.stop();
  } catch (_) {}
  try {
    if (healthMonitor) healthMonitor.stop();
  } catch (_) {}
  try {
    if (tiktokWatchdog) clearInterval(tiktokWatchdog);
    cancelTikTokReconnect('server shutdown');
  } catch (_) {}
  try {
    if (ttsManager) ttsManager.shutdown();
  } catch (_) {}
  try {
    congregation.stop();
  } catch (_) {}
  server.close(() => process.exit(0));
  setTimeout(() => process.exit(0), 1500);
});

