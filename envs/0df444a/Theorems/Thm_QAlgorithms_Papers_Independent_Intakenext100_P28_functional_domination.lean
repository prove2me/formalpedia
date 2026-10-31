-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_functional_domination
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.functional_domination
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:28:08.370847+00:00
-- url     : https://prove2.me/theorems/f9742466-6384-46aa-9a78-b93253566439
-- title:
--   Theorem 1: Functional domination: Df<=kappa_bar Dg, and if f and g are differentiable at 1 with both derivatives zero, the supremal ratio equals kappa_bar
-- statement:
--   Let $f,g$ be convex on $(0,\infty)$, normalized at 1, with $g(t)>0$ for $t\ne1$. Put $\bar\kappa=\sup_{t>0,t\ne1}f(t)/g(t)$, allowing $+\infty$. For every probability pair $P\ll Q$,
--
--   $$D_f(P\|Q)\le\bar\kappa D_g(P\|Q).$$
--
--   If both derivatives at 1 exist and vanish, $\bar\kappa$ is the least universal multiplicative coefficient over all measurable alphabets and probability pairs. This best-constant formulation avoids undefined infinite quotients and retains both parts of Theorem 1.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 13, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 1: Functional domination: Df<=kappa_bar Dg, and if f and g are differentiable at 1 with both derivatives zero, the supremal ratio equals kappa_bar. Sason--Verdu, arXiv:1508.00335v7, PDF p.13.  -/
theorem functional_domination
    (f g : ℝ → ℝ) (hf : Generator f) (hg : PositiveGenerator g)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    fDiv f P Q ≤ (functionalConstant f g : EReal) * fDiv g P Q ∧
    ((HasDerivAt f 0 1 ∧ HasDerivAt g 0 1) →
      Sharp (nDiv f) (nDiv g) acPairs (functionalConstant f g)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
