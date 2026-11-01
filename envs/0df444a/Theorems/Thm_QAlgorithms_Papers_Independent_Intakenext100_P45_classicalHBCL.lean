-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_classicalHBCL
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.classicalHBCL
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:10:59.256875+00:00
-- url     : https://prove2.me/theorems/2518c781-e685-4a6c-9b5f-5f541c49ec74
-- title:
--   Theorem 3, classical HBCL
-- statement:
--   Let $p,q$ be finite equivalent probability laws and $e$ their Hoeffding exponent. For every $r>0$ there is a sequence of randomized tests on IID samples whose extended error rates both exist and obey
--
--   $$\alpha_R=e(r),\qquad\beta_R\ge r.$$
--
--   For every test sequence with both rate limits, $\beta_R>r$ implies $\alpha_R\le e(r)$. Here $\alpha$ accepts the alternative under $p$, and $\beta$ accepts the null under $q$. The strict converse and weak achievability inequalities are retained.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 21, Theorem 3, classical HBCL

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

/-- arXiv:0708.4282v1, PDF pp.20,21: Theorem 3, classical HBCL. -/
theorem classicalHBCL (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q)
    (heq : SamePositiveSupport p q) : ClassicalHBCL p q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
