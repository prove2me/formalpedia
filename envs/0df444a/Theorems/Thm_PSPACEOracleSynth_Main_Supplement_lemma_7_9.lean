-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_lemma_7_9
-- name    : PSPACEOracleSynth.Main.Supplement.lemma_7_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:42:33.31512+00:00
-- url     : https://prove2.me/theorems/303a06ea-1e2b-44e8-832a-1bdb74887f7c
-- title:
--   Lemma 7.9 — Soundness against entangled inputs forces acceptance probabilities to differ by at most (9/2)ε from any input accepted with probability ≥3/4.
-- statement:
--   Fix a verifier satisfying Definition 2.10 soundness with error $\varepsilon$ instead of $1/r$, and fix any prover and initial memory state. Let $p(\psi)$ be its acceptance probability on a pure input to $A_x$. If $p(\psi)\ge3/4$, then for every pure input $\psi'$,
--
--   $$p(\psi')\ge p(\psi)-\frac92\varepsilon.$$
--
--   Soundness includes entangled inputs and channel completions even when the displayed acceptance probabilities concern unentangled inputs. No honest-prover or completeness hypothesis is added.
--
--   Differences from the source:
--   - encoding: states and unit kets in the mathematical definitions → explicit density and unit-norm predicates; reason: these are the standing state conventions, not extra regularity assumptions
--   - encoding: verifier rounds over G including T-dagger → published general-circuit verifier rounds over H,T,CNOT, with T-dagger compiled as seven T gates; reason: the compilation is exact and has constant overhead; prover channels and persistent memory are unrestricted
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Lemma 7.9, p. 42

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Interaction

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement


/-- Lemma 7.9, p. 42: threshold 3/4 and the exact constant 9/2. -/
theorem lemma_7_9 {a b : ℕ} (U : PartialIso a b) (V : Verifier) (ε : ℝ)
    (hV : V.Sound U ε) (P : ProverMoves V.m)
    (τ : Op (Bits P.memory)) (hτ : IsDensityMatrix τ)
    (ψ : Bits a → ℂ) (hψ : UnitKet ψ)
    (hacc : (3 : ℝ)/4 ≤ ((V.accepted P a τ) (ket ψ)).trace.re) :
    ∀ ψ' : Bits a → ℂ, UnitKet ψ' →
      ((V.accepted P a τ) (ket ψ)).trace.re - (9 : ℝ)/2 * ε ≤
        ((V.accepted P a τ) (ket ψ')).trace.re := by sorry

end PSPACEOracleSynth.Main.Supplement
