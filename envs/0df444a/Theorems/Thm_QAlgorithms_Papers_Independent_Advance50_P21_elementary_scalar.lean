-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_elementary_scalar
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.elementary_scalar
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:55:55.201788+00:00
-- url     : https://prove2.me/theorems/5ebcdc81-0f6c-4235-83fb-ad78c50c2486
-- title:
--   Lemma 13: elementary scalar inequality
-- statement:
--   For real numbers $x,y\in[0,1]$,
--   $$xy+\sqrt{x(1-x)y(1-y)}\ge\min\{x,y\}.$$
--   The first term is $xy$, outside the radical. This scalar comparison is used in the spectral-majorization argument and includes all four boundary corners.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 12, Lemma 13: elementary scalar inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.12, Lemma 13, (5.7): only the second summand is under the square root. -/
theorem elementary_scalar (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    min x y ≤ x * y + Real.sqrt (x * (1 - x) * y * (1 - y)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
