-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_one_sided_domination_sharp
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.one_sided_domination_sharp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:50:10.460488+00:00
-- url     : https://prove2.me/theorems/b0abb4f7-b877-4071-918e-04b2c1af8074
-- title:
--   One-sided derivative relaxation of sharp functional domination
-- statement:
--   Under the generator assumptions of Theorem 1, the sharp identity with $\bar\kappa=\sup_{t>0,t\ne1}f(t)/g(t)$ remains valid with one-sided derivatives:
--
--   $$\bar\kappa=\sup_{t>1}\kappa(t)\implies f'_-(1)=g'_-(1)=0\text{ suffices},$$
--
--   and if $\bar\kappa=\sup_{0<t<1}\kappa(t)$, the right derivatives being zero suffice. In either case $\bar\kappa$ is the least universal comparison coefficient over all probability spaces. Both distinct relaxations in Remark 3 are retained.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 14, One-sided derivative relaxation of sharp functional domination

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- One-sided derivative relaxation of sharp functional domination. Sason--Verdu, arXiv:1508.00335v7, PDF p.14.  -/
theorem one_sided_domination_sharp
    (f g : ℝ → ℝ) (hf : Generator f) (hg : PositiveGenerator g) :
    (functionalConstant f g = functionalConstant f g (Ioi 1) →
      HasDerivWithinAt f 0 (Iio 1) 1 → HasDerivWithinAt g 0 (Iio 1) 1 →
      Sharp (nDiv f) (nDiv g) acPairs (functionalConstant f g)) ∧
    (functionalConstant f g = functionalConstant f g (Ioo 0 1) →
      HasDerivWithinAt f 0 (Ioi 1) 1 → HasDerivWithinAt g 0 (Ioi 1) 1 →
      Sharp (nDiv f) (nDiv g) acPairs (functionalConstant f g)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
