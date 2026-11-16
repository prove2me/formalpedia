-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_lemma_7_5
-- name    : PSPACEOracleSynth.Main.Supplement.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:39:45.336866+00:00
-- url     : https://prove2.me/theorems/fdbd34b5-22ec-4e8c-8d04-4794f1a341dc
-- title:
--   Lemma 7.5 — For any acceptance probability, the accepted subnormalized resource and memory state is within 3√ε of a product.
-- statement:
--   Let $V$ be a verifier for a unit pure state $|\chi\rangle$ with error $\varepsilon$. Fix any prover and any independent initial private memory state. Let $\Omega$ be its subnormalized accepted state on the resource output $C$ and memory $M$, including the message register. Define $\rho_M=\langle\chi|\Omega|\chi\rangle$. Then
--
--   $$\|\Omega-\chi\otimes\rho_M\|_1\le3\sqrt{\varepsilon}.$$
--
--   There is no lower bound on this prover's acceptance probability, and $\rho_M$ is not normalized. The statement controls correlations with memory when resource verifiers are reused.
--
--   Differences from the source:
--   - encoding: states, unit kets and error parameters in the mathematical definitions → explicit density, unit-norm and nonnegative-error predicates; reason: these are the standing state and error conventions, not extra regularity assumptions
--   - encoding: verifier rounds over G including T-dagger → published general-circuit verifier rounds over H,T,CNOT, with T-dagger compiled as seven T gates; reason: the compilation is exact and has constant overhead; prover channels and persistent memory are unrestricted
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Lemma 7.5, p. 39

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Interaction

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement


/-- Lemma 7.5, p. 39. No acceptance lower bound is imposed on this prover. -/
theorem lemma_7_5 (V : Verifier) (χ : Bits V.o → ℂ) (ε : ℝ)
    (hV : V.StateVerifier χ ε) (P : ProverMoves V.m)
    (τ : Op (Bits P.memory)) (hτ : IsDensityMatrix τ) :
    let Ω := V.acceptedJoint P 0 τ (ket (fun _ => (1 : ℂ)))
    traceNorm (Ω - (ket χ ⊗ₖ memoryMarginal χ Ω)) ≤ 3 * Real.sqrt ε := by sorry

end PSPACEOracleSynth.Main.Supplement
