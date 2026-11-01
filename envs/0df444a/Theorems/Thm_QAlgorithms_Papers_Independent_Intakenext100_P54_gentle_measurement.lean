-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_gentle_measurement
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.gentle_measurement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:40:43.204759+00:00
-- url     : https://prove2.me/theorems/ee50be14-f65a-4869-87b4-63d1fd8f6505
-- title:
--   Lemma 17: gentle measurement
-- statement:
--   Let $\rho$ be a positive semidefinite trace-one operator on a nonzero finite-dimensional complex Hilbert space. Let $X$ satisfy $0\preceq X\preceq I$, and let $\varepsilon\ge0$. If $\operatorname{Tr}(\rho X)\ge1-\varepsilon$, then
--
--   $$\bigl\|\rho-\sqrt X\rho\sqrt X\bigr\|_1\le\sqrt{8\varepsilon}.$$
--
--   The postmeasurement operator is unnormalized, and $\|\cdot\|_1$ is the Schatten trace norm. This bounds disturbance without dividing by success probability.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 10, Lemma 17: gentle measurement

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal

open MeasureTheory ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P54

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

/-- Lemma 17, PDF p.10: gentle measurement, with the unnormalized postmeasurement operator.
No division by the success probability occurs. -/
theorem gentle_measurement {D : ℕ} (hD : 0 < D)
    (rho X : Matrix (Fin D) (Fin D) ℂ) (hrho : IsDensityMatrix rho)
    (hX : X.PosSemidef) (hXI : (1 - X).PosSemidef)
    (eps : ℝ) (heps : 0 ≤ eps) (hsuccess : 1 - eps ≤ (rho * X).trace.re) :
    traceNorm (rho - cfc Real.sqrt X * rho * cfc Real.sqrt X) ≤ Real.sqrt (8 * eps) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
