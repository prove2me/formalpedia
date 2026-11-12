-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_logSumBounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.logSumBounds
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T06:19:26.007743+00:00
-- url     : https://prove2.me/theorems/329aea3e-e2c9-4966-8157-eaa76b1e6b4b
-- title:
--   Lemma 6, scalar log-sum bounds
-- statement:
--   For positive real scalars $x,y$, with natural logarithms,
--
--   $$\max(\log x,\log y)\le\log(x+y)\le\max(\log x,\log y)+\log2.$$
--
--   This controls the exponential rate of a sum by the larger summand.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 27, Lemma 6, scalar log-sum bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF pp.27,28: Lemma 6, scalar log-sum bounds. -/
theorem logSumBounds (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    max (Real.log x) (Real.log y) ≤ Real.log (x+y) ∧
    Real.log (x+y) ≤ max (Real.log x) (Real.log y)+Real.log 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
