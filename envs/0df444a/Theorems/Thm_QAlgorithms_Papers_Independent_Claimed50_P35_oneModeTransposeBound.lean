-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_oneModeTransposeBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.oneModeTransposeBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:41:44.066088+00:00
-- url     : https://prove2.me/theorems/743a57d0-e639-4eb6-8480-a073298772ea
-- title:
--   V.B, Eq.(5.53): explicit transpose upper bound
-- statement:
--   Let $k,N_c\ge0$ and let $T$ be the actual noisy one-mode channel. If $b=|k^2-1|+2N_c>0$, then
--
--   $$Q_\Theta(T)\le\max\{0,\log_2(k^2+1)-\log_2 b\}.$$
--
--   If $b=0$, the channel is the full oscillator identity and $Q_\Theta(T)=Q(T)=+\infty$. Values are in qubits per use. This is an upper bound; no equality to the finite expression is asserted.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 10, V.B, Eq.(5.53): explicit transpose upper bound

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-- V.B, (5.53), p.10: upper bound, not equality. At the zero denominator,
the complete oscillator identity has infinite capacity; real log0 is not used. -/
theorem oneModeTransposeBound (k Nc : ℝ) (hk : 0 ≤ k) (hNc : 0 ≤ Nc) :
    (0 < |k ^ 2 - 1| + 2 * Nc →
      transposeBound (noisyChannel k Nc) ≤ ENNReal.ofReal
        (max 0 (Real.logb 2 (k ^ 2 + 1) - Real.logb 2 (|k ^ 2 - 1| + 2 * Nc)))) ∧
    (|k ^ 2 - 1| + 2 * Nc = 0 →
      transposeBound (noisyChannel k Nc) = ⊤ ∧ traceClassQuantumCapacity (noisyChannel k Nc) = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
