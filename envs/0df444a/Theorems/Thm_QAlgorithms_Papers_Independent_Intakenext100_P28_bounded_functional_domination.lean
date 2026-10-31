-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_bounded_functional_domination
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.bounded_functional_domination
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:31:04.907151+00:00
-- url     : https://prove2.me/theorems/bcf2848e-6146-4c50-b1ae-31529a99909b
-- title:
--   Theorem 6: Bounded functional domination: Df<=kappa_star Dg, with kappa_star=sup kappa on (beta2,1) union (1,beta1^{-1})
-- statement:
--   Let $f,g$ satisfy the generator assumptions of Theorem 1. For any probability pair, let $\beta_1=\exp_b(-D_\infty(P\|Q))$ and $\beta_2=\exp_b(-D_\infty(Q\|P))$, with $\exp_b(-\infty)=0$. If both betas are less than 1, then
--
--   $$D_f(P\|Q)\le\kappa^*D_g(P\|Q),\qquad
--   \kappa^*=\sup_{t\in(\beta_2,1)\cup(1,\beta_1^{-1})}\frac{f(t)}{g(t)}.$$
--
--   The endpoint $\beta_1^{-1}$ is infinite when $\beta_1=0$. Singular masses use (37); no additional absolute-continuity restriction is imposed.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 24, Theorem 6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 6: Bounded functional domination: Df<=kappa_star Dg, with kappa_star=sup kappa on (beta2,1) union (1,beta1^{-1}). Sason--Verdu, arXiv:1508.00335v7, PDF p.24.  -/
theorem bounded_functional_domination
    (f g : ℝ → ℝ) (hf : Generator f) (hg : PositiveGenerator g)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hb1 : inverseUpperDensity P Q < 1) (hb2 : inverseUpperDensity Q P < 1) :
    fDiv f P Q ≤ (functionalConstant f g (densityInterval P Q) : EReal) * fDiv g P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
