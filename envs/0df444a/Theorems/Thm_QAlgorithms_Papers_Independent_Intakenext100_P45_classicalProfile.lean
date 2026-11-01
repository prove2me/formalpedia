-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_classicalProfile
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.classicalProfile
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:15:39.574177+00:00
-- url     : https://prove2.me/theorems/18acb57d-1f51-479c-9f95-37ec9ced1384
-- title:
--   §5.2, full unequal-support profile
-- statement:
--   For nonorthogonal finite laws, let $a=-\log\psi_1$, $b=-\log\psi_0$, $h=H(\widetilde p\|\widetilde q)$ and $h'=H(\widetilde q\|\widetilde p)$. Then
--
--   $$e(r)=+\infty\ (0\le r<a),\qquad e(a)=b+h'=H(\widetilde q\|p),$$
--   $$a+h=H(\widetilde p\|q),\qquad e(r)=b\ (r\ge a+h).$$
--
--   On $[a,\infty)$ the exponent is finite, convex and non-increasing. If the conditional laws differ, it is strictly convex and strictly decreasing on $[a,a+h]$. If they coincide, it equals $b$ throughout $[a,\infty)$. Conditional laws in entropies against ambient laws are extended by zero outside the overlap.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 24, §5.2, full unequal-support profile

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

/-- arXiv:0708.4282v1, PDF pp.24,25: §5.2, full unequal-support profile. -/
theorem classicalProfile (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q)
    (h0 : 0 < overlapMass p q) (h1 : 0 < overlapMass q p) :
    Profile p q (classicalExponent p q) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
