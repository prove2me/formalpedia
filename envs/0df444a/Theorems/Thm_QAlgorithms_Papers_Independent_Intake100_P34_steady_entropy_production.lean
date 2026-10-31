-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_steady_entropy_production
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.steady_entropy_production
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:15:40.574785+00:00
-- url     : https://prove2.me/theorems/adc41fd1-74dc-4909-98c3-6d07864802e6
-- title:
--   §3.3 Remark 1 — steady entropy production and nonzero flux
-- statement:
--   Assume detailed balance and positivity improvement on the nonzero finite matrix algebra. Set $\bar s=-\nabla e(0)$ and $\sigma_+=\sum_j\bar s_j$. Then $\sigma_+\ge0$. If the reservoir pairs share a time reversal, then
--
--   $$I(-\bar s)=\sigma_+,\qquad\sigma_+>0\ \Longleftrightarrow\ \bar s\ne0.$$
--
--   Here $I$ is the extended-real fluctuation rate function. This identifies strict steady entropy production with a nonzero limiting entropy-transport vector under time reversal.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 8, §3.3 Remark 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF p.8, Remark 1: nonnegative steady entropy production, with the strict iff under TR. -/
theorem steady_entropy_production {d M : ℕ} (D : DBData d M) (hER : ER D) :
    0 ≤ ∑ j, entropyMean D j ∧
    (TR D → rateFunction D (-entropyMean D) = ((∑ j, entropyMean D j : ℝ) : EReal) ∧
      (0 < ∑ j, entropyMean D j ↔ entropyMean D ≠ 0)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
