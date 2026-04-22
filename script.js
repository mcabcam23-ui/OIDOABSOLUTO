const startBtn = document.getElementById("start-btn");
const replayBtn = document.getElementById("replay-btn");
const skipBtn = document.getElementById("skip-btn");
const whiteOnlyToggle = document.getElementById("white-only-toggle");
const whiteOnlyOption = document.getElementById("white-only-option");
const triadNaturalToggle = document.getElementById("triad-natural-toggle");
const triadNaturalOption = document.getElementById("triad-natural-option");
const gameModeSelect = document.getElementById("game-mode-select");
const triadModeSelect = document.getElementById("triad-mode-select");
const inputModeSelect = document.getElementById("input-mode-select");
const micSettings = document.getElementById("mic-settings");
const micSensitivitySelect = document.getElementById("mic-sensitivity-select");
const micBlockSelect = document.getElementById("mic-block-select");
const inputModeStatus = document.getElementById("input-mode-status");
const connectionStatus = document.getElementById("connection-status");
const message = document.getElementById("message");
const overlay = document.getElementById("overlay");
const roundEl = document.getElementById("round");
const hitsEl = document.getElementById("hits");
const attemptsEl = document.getElementById("attempts");
const accuracyEl = document.getElementById("accuracy");

const MIN_MIDI_NOTE = 36; // C2
const MAX_MIDI_NOTE = 85; // C6 (50 notas exactas)

let audioContext = null;
let midiAccess = null;
let activeInput = null;
let targetNote = null;
let rounds = 0;
let hits = 0;
let attempts = 0;
let isRunning = false;
let whiteOnlyMode = false;
let waitingNextRound = false;
let inputMode = "microphone";
let gameMode = "single";
let triadMode = "mixed";
let triadNaturalOnlyMode = true;
let targetChordNotes = null;
let targetChordPitchClasses = null;
let previousSingleNote = null;
let previousChordSignature = null;
let chordGuessPitchClasses = new Set();
let chordGuessTimer = null;
let singleGuessLockedNote = null;
const midiHeldNotes = new Set();

let micStream = null;
let micSource = null;
let micAnalyser = null;
let micBuffer = null;
let micAnimationFrame = null;
let stableDetectedNote = null;
let stableFrames = 0;
let lastDetectedAt = 0;
let micIgnoreUntilMs = 0;
let micStableFramesRequired = 3;
let micDetectionCooldownMs = 350;
let micBlockExtraMs = 900;
let micNeedsQuietOnset = true;
let micSilenceAccumMs = 0;
let micLastFrameAtMs = 0;
let micSilenceRequiredMs = 260;
let micSilenceRmsThreshold = 0.011;
let micMinDetectRms = 0.016;
let micPrevRms = 0;
let micAttackArmed = false;
let micAttackWindowUntilMs = 0;
let hammerNoiseBuffer = null;
let pianoSampler = null;
let samplerReady = false;

const NOTE_NAMES = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"];
const PIANO_SAMPLE_URLS = {
  A0: "A0.mp3",
  C1: "C1.mp3",
  "D#1": "Ds1.mp3",
  "F#1": "Fs1.mp3",
  A1: "A1.mp3",
  C2: "C2.mp3",
  "D#2": "Ds2.mp3",
  "F#2": "Fs2.mp3",
  A2: "A2.mp3",
  C3: "C3.mp3",
  "D#3": "Ds3.mp3",
  "F#3": "Fs3.mp3",
  A3: "A3.mp3",
  C4: "C4.mp3",
  "D#4": "Ds4.mp3",
  "F#4": "Fs4.mp3",
  A4: "A4.mp3",
  C5: "C5.mp3",
  "D#5": "Ds5.mp3",
  "F#5": "Fs5.mp3",
  A5: "A5.mp3",
  C6: "C6.mp3",
  "D#6": "Ds6.mp3",
  "F#6": "Fs6.mp3",
  A6: "A6.mp3",
  C7: "C7.mp3",
  "D#7": "Ds7.mp3",
  "F#7": "Fs7.mp3",
  A7: "A7.mp3",
  C8: "C8.mp3",
};

function midiToFrequency(midiNote) {
  return 440 * 2 ** ((midiNote - 69) / 12);
}

function frequencyToMidi(frequency) {
  return Math.round(69 + 12 * Math.log2(frequency / 440));
}

function midiToNoteName(midiNote) {
  const pitchClass = NOTE_NAMES[midiNote % 12];
  const octave = Math.floor(midiNote / 12) - 1;
  return `${pitchClass}${octave}`;
}

function toPitchClass(midiNote) {
  const normalized = midiNote % 12;
  return normalized < 0 ? normalized + 12 : normalized;
}

async function ensurePianoSampler() {
  if (samplerReady && pianoSampler) return true;
  if (typeof Tone === "undefined") return false;

  try {
    await Tone.start();
    if (!pianoSampler) {
      pianoSampler = new Tone.Sampler({
        urls: PIANO_SAMPLE_URLS,
        release: 2.2,
        baseUrl: "https://tonejs.github.io/audio/salamander/",
      }).toDestination();
    }
    await Tone.loaded();
    samplerReady = true;
    return true;
  } catch (error) {
    samplerReady = false;
    console.error("No se pudo cargar el sampler de piano:", error);
    return false;
  }
}

function createHammerNoiseBuffer() {
  if (!audioContext) return null;
  const length = Math.floor(audioContext.sampleRate * 0.08);
  const buffer = audioContext.createBuffer(1, length, audioContext.sampleRate);
  const channel = buffer.getChannelData(0);
  for (let i = 0; i < length; i += 1) {
    channel[i] = (Math.random() * 2 - 1) * (1 - i / length);
  }
  return buffer;
}

function blockMicDetectionFor(durationSeconds, extraMs = micBlockExtraMs) {
  const blockMs = Math.max(0, Math.round(durationSeconds * 1000) + extraMs);
  micIgnoreUntilMs = Math.max(micIgnoreUntilMs, Date.now() + blockMs);
  micNeedsQuietOnset = true;
  micSilenceAccumMs = 0;
  micPrevRms = 0;
  micAttackArmed = false;
  micAttackWindowUntilMs = 0;
  stableDetectedNote = null;
  stableFrames = 0;
}

function playPianoLikeNote(midiNote, duration = 1.0) {
  if (samplerReady && pianoSampler) {
    const playedDuration = Math.max(1.0, duration);
    blockMicDetectionFor(playedDuration);
    const noteName = midiToNoteName(midiNote);
    pianoSampler.triggerAttackRelease(noteName, playedDuration, undefined, 0.95);
    return;
  }

  playFallbackPianoNote(midiNote, duration);
}

function playTriadChord(notes, duration = 2.4) {
  notes.forEach((note) => {
    playPianoLikeNote(note, duration);
  });
}

function playFallbackPianoNote(midiNote, duration = 1.0) {
  if (!audioContext) return;

  const now = audioContext.currentTime;
  const baseFreq = midiToFrequency(midiNote);
  const noteBrightness = Math.min(1, Math.max(0, (midiNote - 24) / 72));
  const noteDuration = Math.max(1.0, duration);
  blockMicDetectionFor(noteDuration);

  const master = audioContext.createGain();
  master.gain.setValueAtTime(0.0001, now);
  master.gain.linearRampToValueAtTime(0.72, now + 0.005);
  master.gain.exponentialRampToValueAtTime(0.24, now + 0.3);
  master.gain.setValueAtTime(0.24, now + 0.9);
  master.gain.exponentialRampToValueAtTime(0.0001, now + noteDuration);

  const bodyFilter = audioContext.createBiquadFilter();
  bodyFilter.type = "lowpass";
  bodyFilter.frequency.setValueAtTime(2200 + noteBrightness * 2800, now);
  bodyFilter.Q.value = 0.75;

  const resonance = audioContext.createBiquadFilter();
  resonance.type = "peaking";
  resonance.frequency.setValueAtTime(260 + baseFreq * 0.35, now);
  resonance.Q.value = 1.4;
  resonance.gain.value = 4;

  const output = audioContext.createGain();
  output.gain.value = 0.92;

  master.connect(bodyFilter);
  bodyFilter.connect(resonance);
  resonance.connect(output);
  output.connect(audioContext.destination);

  // Totalmente afinado: sin detune entre cuerdas.
  const unisonDetune = [0];
  unisonDetune.forEach((cents, index) => {
    const osc = audioContext.createOscillator();
    const gain = audioContext.createGain();
    osc.type = "triangle";
    osc.frequency.setValueAtTime(baseFreq, now);
    osc.detune.setValueAtTime(cents, now);

    const stringLevel = 0.47 / unisonDetune.length + (index === 1 ? 0.02 : 0);
    gain.gain.setValueAtTime(0.0001, now);
    gain.gain.linearRampToValueAtTime(stringLevel, now + 0.004);
    gain.gain.exponentialRampToValueAtTime(0.13, now + 0.28);
    gain.gain.setValueAtTime(0.13, now + 0.85);
    gain.gain.exponentialRampToValueAtTime(0.0001, now + noteDuration);

    osc.connect(gain);
    gain.connect(master);
    osc.start(now);
    osc.stop(now + noteDuration + 0.05);
  });

  const partials = [
    { mul: 2.0, gain: 0.13 },
    { mul: 3.0, gain: 0.085 },
    { mul: 4.0, gain: 0.045 },
    { mul: 5.0, gain: 0.025 },
  ];
  partials.forEach((partial) => {
    const osc = audioContext.createOscillator();
    const gain = audioContext.createGain();
    osc.type = "sine";
    osc.frequency.setValueAtTime(baseFreq * partial.mul, now);
    gain.gain.setValueAtTime(0.0001, now);
    gain.gain.linearRampToValueAtTime(partial.gain * (0.65 + noteBrightness * 0.5), now + 0.003);
    gain.gain.exponentialRampToValueAtTime(0.0001, now + 1.4 + (1 - noteBrightness) * 0.35);
    osc.connect(gain);
    gain.connect(master);
    osc.start(now);
    osc.stop(now + noteDuration + 0.02);
  });

  // Ruido breve del martillo para el ataque característico.
  if (!hammerNoiseBuffer) {
    hammerNoiseBuffer = createHammerNoiseBuffer();
  }
  if (hammerNoiseBuffer) {
    const noise = audioContext.createBufferSource();
    noise.buffer = hammerNoiseBuffer;

    const hp = audioContext.createBiquadFilter();
    hp.type = "highpass";
    hp.frequency.value = 900;
    const bp = audioContext.createBiquadFilter();
    bp.type = "bandpass";
    bp.frequency.value = 1800 + noteBrightness * 1400;
    bp.Q.value = 0.9;

    const noiseGain = audioContext.createGain();
    noiseGain.gain.setValueAtTime(0.0001, now);
    noiseGain.gain.linearRampToValueAtTime(0.07 + noteBrightness * 0.06, now + 0.002);
    noiseGain.gain.exponentialRampToValueAtTime(0.0001, now + 0.04);

    noise.connect(hp);
    hp.connect(bp);
    bp.connect(noiseGain);
    noiseGain.connect(master);
    noise.start(now);
    noise.stop(now + 0.05);
  }
}

function randomMidiNote() {
  return Math.floor(Math.random() * (MAX_MIDI_NOTE - MIN_MIDI_NOTE + 1)) + MIN_MIDI_NOTE;
}

function isWhiteKey(midiNote) {
  const noteInOctave = midiNote % 12;
  return [0, 2, 4, 5, 7, 9, 11].includes(noteInOctave);
}

function randomTargetNote() {
  if (!whiteOnlyMode) {
    return randomMidiNote();
  }

  const whiteKeys = [];
  for (let note = MIN_MIDI_NOTE; note <= MAX_MIDI_NOTE; note += 1) {
    if (isWhiteKey(note)) {
      whiteKeys.push(note);
    }
  }
  const randomIndex = Math.floor(Math.random() * whiteKeys.length);
  return whiteKeys[randomIndex];
}

function randomTargetNoteWithoutImmediateRepeat() {
  const MAX_TRIES = 20;
  let nextNote = randomTargetNote();
  for (let i = 0; i < MAX_TRIES && previousSingleNote !== null && nextNote === previousSingleNote; i += 1) {
    nextNote = randomTargetNote();
  }
  previousSingleNote = nextNote;
  return nextNote;
}

function randomTriadQuality() {
  if (triadMode === "major") return "major";
  if (triadMode === "minor") return "minor";
  return Math.random() < 0.5 ? "major" : "minor";
}

function updateGameModeOptionsVisibility() {
  const isTriadMode = gameModeSelect.value === "triad";
  whiteOnlyOption.hidden = isTriadMode;
  triadNaturalOption.hidden = !isTriadMode;
  whiteOnlyOption.style.display = isTriadMode ? "none" : "flex";
  triadNaturalOption.style.display = isTriadMode ? "flex" : "none";
  if (isTriadMode) {
    whiteOnlyToggle.checked = false;
    whiteOnlyMode = false;
  }
}

function updateInputModeVisibility() {
  const isMicInput = inputModeSelect.value === "microphone";
  micSettings.hidden = !isMicInput;
  micSettings.style.display = isMicInput ? "block" : "none";
}

function applyMicrophoneSettings() {
  const sensitivity = micSensitivitySelect.value;
  if (sensitivity === "high") {
    micStableFramesRequired = 2;
    micDetectionCooldownMs = 220;
    micSilenceRequiredMs = 180;
    micSilenceRmsThreshold = 0.012;
    micMinDetectRms = 0.012;
  } else if (sensitivity === "low") {
    micStableFramesRequired = 4;
    micDetectionCooldownMs = 500;
    micSilenceRequiredMs = 360;
    micSilenceRmsThreshold = 0.010;
    micMinDetectRms = 0.022;
  } else {
    micStableFramesRequired = 3;
    micDetectionCooldownMs = 350;
    micSilenceRequiredMs = 260;
    micSilenceRmsThreshold = 0.011;
    micMinDetectRms = 0.016;
  }

  const blockValue = Number.parseInt(micBlockSelect.value, 10);
  micBlockExtraMs = Number.isFinite(blockValue) ? blockValue : 900;
}

function getBufferRms(buffer) {
  let rms = 0;
  for (let i = 0; i < buffer.length; i += 1) {
    const value = buffer[i];
    rms += value * value;
  }
  return Math.sqrt(rms / buffer.length);
}

function createTriadTarget() {
  const naturalRootPitchClasses = [0, 2, 4, 5, 7, 9, 11]; // Do Re Mi Fa Sol La Si
  const allRootPitchClasses = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
  const allowedRoots = triadNaturalOnlyMode ? naturalRootPitchClasses : allRootPitchClasses;
  const randomRootPitchClass = allowedRoots[Math.floor(Math.random() * allowedRoots.length)];
  const rootMidi = 48 + randomRootPitchClass; // C3-B3
  const quality = randomTriadQuality();
  const intervals = quality === "major" ? [0, 4, 7] : [0, 3, 7];
  const notes = intervals.map((interval) => rootMidi + interval);
  const pitchClasses = intervals.map((interval) => toPitchClass(rootMidi + interval)).sort((a, b) => a - b);
  return { notes, pitchClasses, quality };
}

function createTriadTargetWithoutImmediateRepeat() {
  const MAX_TRIES = 20;
  let triad = createTriadTarget();
  let signature = `${triad.quality}:${triad.pitchClasses.join("-")}`;
  for (let i = 0; i < MAX_TRIES && previousChordSignature !== null && signature === previousChordSignature; i += 1) {
    triad = createTriadTarget();
    signature = `${triad.quality}:${triad.pitchClasses.join("-")}`;
  }
  previousChordSignature = signature;
  return triad;
}

function flashOverlay(type, milliseconds) {
  overlay.className = `overlay show ${type}`;
  window.setTimeout(() => {
    overlay.className = "overlay";
  }, milliseconds);
}

function updateStats() {
  roundEl.textContent = String(rounds);
  hitsEl.textContent = String(hits);
  attemptsEl.textContent = String(attempts);
  const acc = attempts === 0 ? 0 : Math.round((hits / attempts) * 100);
  accuracyEl.textContent = `${acc}%`;
}

function beginRound() {
  if (chordGuessTimer) {
    window.clearTimeout(chordGuessTimer);
    chordGuessTimer = null;
  }
  chordGuessPitchClasses.clear();
  singleGuessLockedNote = null;

  waitingNextRound = false;
  rounds += 1;
  updateStats();

  if (gameMode === "triad") {
    const triad = createTriadTargetWithoutImmediateRepeat();
    targetChordNotes = triad.notes;
    targetChordPitchClasses = triad.pitchClasses;
    targetNote = null;
    const triadTypeLabel = triad.quality === "major" ? "mayor" : "menor";
    message.textContent = triadNaturalOnlyMode
      ? `Escucha y toca el acorde (puedes tocarlo por notas). Tipo: ${triadTypeLabel}. Solo Do, Re, Mi, Fa, Sol, La, Si.`
      : `Escucha y toca el acorde (puedes tocarlo por notas). Tipo: ${triadTypeLabel}. Incluye sostenidos y bemoles.`;
    playTriadChord(targetChordNotes, 2.8);
    return;
  }

  targetChordNotes = null;
  targetChordPitchClasses = null;
  targetNote = randomTargetNoteWithoutImmediateRepeat();
  message.textContent = whiteOnlyMode
    ? "Escucha y toca la nota correcta (solo teclas blancas)."
    : "Escucha y toca la nota correcta en tu piano.";
  playPianoLikeNote(targetNote);
}

function handleSingleGuess(note) {
  if (!isRunning || targetNote === null || waitingNextRound || gameMode !== "single") return;
  if (singleGuessLockedNote === note) return;

  singleGuessLockedNote = note;
  attempts += 1;
  if (note === targetNote) {
    waitingNextRound = true;
    hits += 1;
    updateStats();
    message.textContent = "Correcto. Preparando la siguiente nota...";
    flashOverlay("success", 650);
    window.setTimeout(() => {
      beginRound();
    }, 700);
    return;
  }

  updateStats();
  message.textContent = "No es esa. Intenta otra vez.";
  flashOverlay("error", 1000);
}

function evaluateChordGuess() {
  if (!targetChordPitchClasses || waitingNextRound || gameMode !== "triad") return;
  if (chordGuessPitchClasses.size < 3) return;

  attempts += 1;
  const guess = [...chordGuessPitchClasses].sort((a, b) => a - b);
  const isCorrect = guess.every((pc, index) => pc === targetChordPitchClasses[index]);

  if (isCorrect) {
    waitingNextRound = true;
    hits += 1;
    updateStats();
    message.textContent = "Acorde correcto. Preparando el siguiente...";
    flashOverlay("success", 650);
    chordGuessPitchClasses.clear();
    window.setTimeout(() => {
      beginRound();
    }, 700);
    return;
  }

  updateStats();
  message.textContent = "No coincide el acorde. Intenta otra vez.";
  flashOverlay("error", 1000);
  chordGuessPitchClasses.clear();
}

function pushChordGuessNote(note) {
  if (!isRunning || waitingNextRound || gameMode !== "triad") return;
  if (!targetChordPitchClasses) return;

  chordGuessPitchClasses.add(toPitchClass(note));
  if (chordGuessPitchClasses.size >= 3) {
    evaluateChordGuess();
    return;
  }

  if (chordGuessTimer) {
    window.clearTimeout(chordGuessTimer);
  }
  chordGuessTimer = window.setTimeout(() => {
    evaluateChordGuess();
  }, 1200);
}

function handleGuess(note) {
  if (gameMode === "triad") {
    pushChordGuessNote(note);
    return;
  }
  handleSingleGuess(note);
}

function handleMidiMessage(event) {
  const [status, note, velocity] = event.data;
  const command = status & 0xf0;
  const isNoteOff = command === 0x80 || (command === 0x90 && velocity === 0);
  const isNoteOn = command === 0x90 && velocity > 0;
  if (isNoteOff) {
    midiHeldNotes.delete(note);
    if (singleGuessLockedNote === note) {
      singleGuessLockedNote = null;
    }
    return;
  }
  if (!isRunning || targetNote === null || waitingNextRound) return;
  if (!isNoteOn) return;
  if (midiHeldNotes.has(note)) return;
  midiHeldNotes.add(note);

  handleGuess(note);
}

function attachInput(input) {
  if (activeInput) {
    activeInput.onmidimessage = null;
  }

  activeInput = input;
  if (activeInput) {
    activeInput.onmidimessage = handleMidiMessage;
    connectionStatus.textContent = `MIDI conectado: ${activeInput.name || "Dispositivo MIDI"}`;
  } else {
    connectionStatus.textContent = "No hay entrada MIDI disponible";
  }
}

function stopMidiInput() {
  if (activeInput) {
    activeInput.onmidimessage = null;
    activeInput = null;
  }
  midiHeldNotes.clear();
}

function pickFirstMidiInput() {
  if (!midiAccess) return null;
  const first = midiAccess.inputs.values().next();
  return first.done ? null : first.value;
}

async function initializeMidi() {
  if (!navigator.requestMIDIAccess) {
    throw new Error("Este navegador no soporta Web MIDI.");
  }

  midiAccess = await navigator.requestMIDIAccess();
  attachInput(pickFirstMidiInput());

  midiAccess.onstatechange = () => {
    if (!activeInput || activeInput.state !== "connected") {
      attachInput(pickFirstMidiInput());
      return;
    }

    const refreshed = [...midiAccess.inputs.values()].find((input) => input.id === activeInput.id);
    attachInput(refreshed || pickFirstMidiInput());
  };
}

function autoCorrelate(buffer, sampleRate) {
  let rms = 0;
  for (let i = 0; i < buffer.length; i += 1) {
    const value = buffer[i];
    rms += value * value;
  }
  rms = Math.sqrt(rms / buffer.length);
  if (rms < 0.01) return -1;

  let bestOffset = -1;
  let bestCorrelation = 0;
  const maxSamples = Math.floor(buffer.length / 2);
  for (let offset = 8; offset < maxSamples; offset += 1) {
    let correlation = 0;
    for (let i = 0; i < maxSamples; i += 1) {
      correlation += Math.abs(buffer[i] - buffer[i + offset]);
    }
    correlation = 1 - correlation / maxSamples;
    if (correlation > bestCorrelation) {
      bestCorrelation = correlation;
      bestOffset = offset;
    }
  }

  if (bestCorrelation > 0.9 && bestOffset > 0) {
    return sampleRate / bestOffset;
  }
  return -1;
}

function stopMicrophoneDetection() {
  if (micAnimationFrame) {
    cancelAnimationFrame(micAnimationFrame);
    micAnimationFrame = null;
  }
  if (micSource) {
    micSource.disconnect();
    micSource = null;
  }
  if (micStream) {
    micStream.getTracks().forEach((track) => track.stop());
    micStream = null;
  }
  micAnalyser = null;
  micBuffer = null;
  stableDetectedNote = null;
  stableFrames = 0;
  micIgnoreUntilMs = 0;
  micNeedsQuietOnset = true;
  micSilenceAccumMs = 0;
  micLastFrameAtMs = 0;
  micPrevRms = 0;
  micAttackArmed = false;
  micAttackWindowUntilMs = 0;
  singleGuessLockedNote = null;
}

function runMicrophoneLoop() {
  if (!micAnalyser || !micBuffer || inputMode !== "microphone") return;

  const nowMs = performance.now();
  const frameDeltaMs = micLastFrameAtMs > 0 ? nowMs - micLastFrameAtMs : 16;
  micLastFrameAtMs = nowMs;

  if (Date.now() < micIgnoreUntilMs) {
    micNeedsQuietOnset = true;
    micSilenceAccumMs = 0;
    micAttackArmed = false;
    micAttackWindowUntilMs = 0;
    micPrevRms = 0;
    stableDetectedNote = null;
    stableFrames = 0;
    micAnimationFrame = requestAnimationFrame(runMicrophoneLoop);
    return;
  }

  micAnalyser.getFloatTimeDomainData(micBuffer);
  const rms = getBufferRms(micBuffer);

  // Tras reproducir audio, exigimos un breve tramo de silencio del micro
  // antes de volver a aceptar notas. Esto reduce la autocaptura del altavoz.
  if (micNeedsQuietOnset) {
    if (rms < micSilenceRmsThreshold) {
      singleGuessLockedNote = null;
      micSilenceAccumMs += frameDeltaMs;
    } else {
      micSilenceAccumMs = 0;
    }

    if (micSilenceAccumMs < micSilenceRequiredMs) {
      micPrevRms = rms;
      stableDetectedNote = null;
      stableFrames = 0;
      micAnimationFrame = requestAnimationFrame(runMicrophoneLoop);
      return;
    }

    micNeedsQuietOnset = false;
    micSilenceAccumMs = 0;
  }

  if (rms < micMinDetectRms) {
    if (rms < micSilenceRmsThreshold) {
      singleGuessLockedNote = null;
    }
    micPrevRms = rms;
    stableDetectedNote = null;
    stableFrames = 0;
    micAnimationFrame = requestAnimationFrame(runMicrophoneLoop);
    return;
  }

  // En nota individual, solo aceptamos detecciones tras un ataque nuevo
  // (subida de energía), para evitar autocaptura de la cola del altavoz.
  if (gameMode === "single") {
    const attackThreshold = micMinDetectRms * 1.35;
    const hasNewAttack = micPrevRms < micSilenceRmsThreshold && rms >= attackThreshold;
    if (!micAttackArmed && hasNewAttack) {
      micAttackArmed = true;
      micAttackWindowUntilMs = Date.now() + 1400;
      stableDetectedNote = null;
      stableFrames = 0;
    }

    if (!micAttackArmed || Date.now() > micAttackWindowUntilMs) {
      micPrevRms = rms;
      stableDetectedNote = null;
      stableFrames = 0;
      micAnimationFrame = requestAnimationFrame(runMicrophoneLoop);
      return;
    }
  }

  const frequency = autoCorrelate(micBuffer, audioContext.sampleRate);
  if (frequency > 0) {
    const midiNote = frequencyToMidi(frequency);
    if (midiNote >= MIN_MIDI_NOTE && midiNote <= MAX_MIDI_NOTE) {
      if (stableDetectedNote === midiNote) {
        stableFrames += 1;
      } else {
        stableDetectedNote = midiNote;
        stableFrames = 1;
      }

      const now = Date.now();
      if (stableFrames >= micStableFramesRequired && now - lastDetectedAt > micDetectionCooldownMs) {
        lastDetectedAt = now;
        handleGuess(midiNote);
        if (gameMode === "single") {
          micAttackArmed = false;
          micAttackWindowUntilMs = 0;
        }
      }
    }
  } else {
    stableDetectedNote = null;
    stableFrames = 0;
  }

  micPrevRms = rms;
  micAnimationFrame = requestAnimationFrame(runMicrophoneLoop);
}

async function initializeMicrophone() {
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
    throw new Error("Este navegador no soporta acceso a micrófono.");
  }

  stopMicrophoneDetection();
  micStream = await navigator.mediaDevices.getUserMedia({
    audio: {
      echoCancellation: true,
      noiseSuppression: true,
      autoGainControl: true,
    },
    video: false,
  });

  micSource = audioContext.createMediaStreamSource(micStream);
  micAnalyser = audioContext.createAnalyser();
  micAnalyser.fftSize = 2048;
  micBuffer = new Float32Array(micAnalyser.fftSize);
  micSource.connect(micAnalyser);
  micNeedsQuietOnset = true;
  micSilenceAccumMs = 0;
  micLastFrameAtMs = 0;
  micPrevRms = 0;
  micAttackArmed = false;
  micAttackWindowUntilMs = 0;
  connectionStatus.textContent = "Micrófono activo";
  runMicrophoneLoop();
}

async function startGame() {
  startBtn.disabled = true;

  try {
    if (!audioContext) {
      audioContext = new window.AudioContext();
    }

    if (audioContext.state === "suspended") {
      await audioContext.resume();
    }
    await ensurePianoSampler();

    stopMicrophoneDetection();
    stopMidiInput();
    if (chordGuessTimer) {
      window.clearTimeout(chordGuessTimer);
      chordGuessTimer = null;
    }
    chordGuessPitchClasses.clear();
    singleGuessLockedNote = null;
    rounds = 0;
    hits = 0;
    attempts = 0;
    updateStats();

    inputMode = inputModeSelect.value;
    gameMode = gameModeSelect.value;
    triadMode = triadModeSelect.value;
    triadNaturalOnlyMode = triadNaturalToggle.checked;
    applyMicrophoneSettings();
    inputModeStatus.textContent = inputMode === "microphone" ? "Micrófono" : "MIDI";

    if (inputMode === "microphone") {
      await initializeMicrophone();
    } else {
      stopMicrophoneDetection();
      await initializeMidi();
      if (!activeInput) {
        throw new Error("No se detectó ningún piano/controlador MIDI.");
      }
    }

    isRunning = true;
    startBtn.disabled = false;
    startBtn.textContent = "Reiniciar juego";
    replayBtn.disabled = false;
    skipBtn.disabled = false;
    message.textContent = samplerReady
      ? "Juego iniciado."
      : "Juego iniciado (sonido básico, no se pudo cargar el piano real).";
    beginRound();
  } catch (error) {
    isRunning = false;
    startBtn.disabled = false;
    startBtn.textContent = "Iniciar juego";
    message.textContent = error.message;
    connectionStatus.textContent = "Error";
  }
}

startBtn.addEventListener("click", () => {
  startGame();
});

replayBtn.addEventListener("click", () => {
  if (!isRunning) return;
  if (gameMode === "triad") {
    if (!targetChordNotes) return;
    playTriadChord(targetChordNotes, 2.8);
    return;
  }
  if (targetNote === null) return;
  playPianoLikeNote(targetNote);
});

skipBtn.addEventListener("click", () => {
  if (!isRunning) return;
  message.textContent = gameMode === "triad" ? "Acorde saltado. Nueva ronda." : "Nota saltada. Nueva ronda.";
  beginRound();
});

whiteOnlyToggle.addEventListener("change", () => {
  whiteOnlyMode = whiteOnlyToggle.checked;
  if (!isRunning) return;
  message.textContent = whiteOnlyMode
    ? "Modo solo blancas activado. Generando nueva nota."
    : "Modo completo activado. Generando nueva nota.";
  beginRound();
});

inputModeSelect.addEventListener("change", () => {
  updateInputModeVisibility();
  if (isRunning) {
    message.textContent = "El cambio de entrada se aplicará al reiniciar la partida.";
  }
});

gameModeSelect.addEventListener("change", () => {
  updateGameModeOptionsVisibility();
  if (isRunning) {
    message.textContent = "El cambio de modo de juego se aplicará al reiniciar la partida.";
  }
});

triadModeSelect.addEventListener("change", () => {
  if (isRunning) {
    message.textContent = "El tipo de acordes se aplicará al reiniciar la partida.";
  }
});

triadNaturalToggle.addEventListener("change", () => {
  triadNaturalOnlyMode = triadNaturalToggle.checked;
  if (isRunning) {
    message.textContent = "La selección de acordes naturales/sostenidos se aplicará al reiniciar la partida.";
  }
});

updateGameModeOptionsVisibility();
updateInputModeVisibility();
