-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_lemma_7_6
-- name    : PSPACEOracleSynth.Main.Supplement.lemma_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:40:36.092105+00:00
-- url     : https://prove2.me/theorems/ecedd58d-1347-47a3-b496-258b95b94c59
-- title:
--   Lemma 7.6 — Adaptive composition against a persistent prover: conditioned trace error at most 3 n_inj √ε / p_acc.
-- statement:
--   Begin with a state $\psi_0$ on private register $X$ and an untouched reference $R$, in product with the prover's initial memory. In each of $n_{\rm inj}$ adaptive steps, run a fresh pure-state verifier with common error $\varepsilon$, retain its acceptance bit, apply the history-dependent instrument to $X$ and its resource output, and transmit the outcome history to the persistent prover. Accept if every retained bit accepts. Suppose every positive-probability complete history in the exact-resource run leaves the same state $\psi'$ on $XR$. For every prover with final acceptance probability $p_{\rm acc}>0$, its normalized accepted state $\sigma$ satisfies
--
--   $$D(\sigma,\psi')\le\frac{3n_{\rm inj}\sqrt{\varepsilon}}{p_{\rm acc}}.$$
--
--   The bound permits adaptive targets and instruments, changing private-register sizes, arbitrary retained memory and arbitrarily small acceptance in individual calls.
--
--   Differences from the source:
--   - encoding: adaptive finite histories of verifier calls and instruments with retained acceptance bits → a finite dependent outcome tree, unrestricted Kraus instruments and composition of accepted branches; reason: retained acceptance bits are never subsequently acted on, so their conjunction is exactly the composition of accepted branches; all memory and reference coherences are kept
--   - generalization: initial state ψ0 of XR and final state ψ′ (written as pure states) → arbitrary density matrices ψ₀ and ψ′; reason: pure states are density matrices, so the statement specializes to the source; the application in the proof of Theorem 7.1 (p. 41) needs mixed ψ0 after measurements
--   - encoding: states and unit kets in the mathematical definitions → explicit density and unit-norm predicates; reason: these are the standing state conventions, not extra regularity assumptions
--   - encoding: verifier rounds over G including T-dagger → published general-circuit verifier rounds over H,T,CNOT, with T-dagger compiled as seven T gates; reason: the compilation is exact and has constant overhead; prover channels and persistent memory are unrestricted
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Lemma 7.6, p. 40

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Adaptive

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement


/-- Lemma 7.6, pp. 40–41: adaptive calls, persistent memory and a positive
final acceptance probability; the numerical bound is trace distance, not trace norm. -/
theorem lemma_7_6 {n x out r y : ℕ} (T : ResourceTree n x out) (ε : ℝ)
    (hT : T.Valid ε)
    (ψ₀ : Op (Bits x × Bits r)) (hψ₀ : IsDensityMatrix ψ₀)
    (ψ' : Op (Bits out × Bits r)) (hψ' : IsDensityMatrix ψ')
    (hideal : T.OutcomeIndependent ψ₀ ψ') (P : TreeProver y)
    (τ : Op (Bits y)) (hτ : IsDensityMatrix τ)
    (hacc : 0 < (forgetMemory (T.run P [] (independentStart ψ₀ τ))).trace.re) :
    let Ω := forgetMemory (T.run P [] (independentStart ψ₀ τ))
    dist (normalized Ω) ψ' ≤ 3 * n * Real.sqrt ε / Ω.trace.re := by sorry

end PSPACEOracleSynth.Main.Supplement
