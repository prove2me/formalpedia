-- Prove2me | Theorems.Thm_SunkCost_SmallBias_optimal_price_eq_max
-- name    : SunkCost.SmallBias.optimal_price_eq_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:45.295237+00:00
-- url     : https://prove2.me/theorems/d38dd729-c295-4d9e-84c3-a47285e64800
-- title:
--   §4.2, pp. 10, 12 (PDF 11, 13) — for λ < λ1 the optimal price is max(p̂a, pr)
-- statement:
--   Let the standing assumptions hold, let $F$ be a valuation distribution with support $(0,1)$, and let $0\le\lambda<\lambda_1$. Suppose that the objective $p\mapsto(p-c)(1-F(v_3))$ of (7) is strictly concave on $[0,(1-\kappa)\alpha]$, that $p_r$ maximizes it over all real $p$, and that $c<\hat p_a$. Then a price $p$ is optimal for the firm if and only if
--
--   $$p=\max(\hat p_a,\,p_r).$$
--
--   In particular an optimal price exists and is unique. Below $\hat p_a$ demand increases in price, so the firm never prices below $\hat p_a$; above $\hat p_a$ the profit is the objective of (7). This is the optimal price on which Proposition 3 rests: "for low values of $\lambda$, the optimal price is $\hat p_a$" (p. 10).
--
--   **Formalization Note.** The paper's assumption "the profit function is strictly concave" (p. 10) is imposed on $[0,(1-\kappa)\alpha]$, the prices at which $1-F(v_3)>0$; beyond it the objective vanishes identically and cannot be strictly concave. The price $p_r$ is a variable pinned by the hypothesis that it maximizes (7), not an arg max. The paper spells the argument out on p. 12, in the discussion of Proposition 5, where it does not depend on the regime.
-- source:
--   Jain and Chen, Sunk cost bias and time inconsistency: a strategic analysis of pricing decisions, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4479, p. 10 (PDF 11), §4.2 ('The proposition shows that, for low values of λ, the optimal price is p̂a'), and p. 12 (PDF 13), discussion of Proposition 5 ('If pr < p̂a, then the firm again faces an increasing demand function ... p̂a must be the optimal price.'); eq. (7)

import Mathlib
import Definitions.Def_SunkCost_SmallBias_Model

namespace SunkCost.SmallBias

/-- §4.2, p. 10 (PDF 11), and the discussion of Proposition 5, p. 12 (PDF 13): for
`0 ≤ λ < λ₁`, if the objective `(p − c)(1 − F(v₃))` of (7) is strictly concave on
`[0, (1 − κ)α]`, `p_r` maximizes it, and `c < p̂_a`, then the optimal prices are exactly
`max(p̂_a, p_r)`. -/
theorem optimal_price_eq_max (P : Params) (hS : P.Standing) (F : StieltjesFunction ℝ)
    (hF : ValuationCDF F) (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < lam1 P) (pr : ℝ)
    (hconc : StrictConcaveOn ℝ (Set.Icc 0 ((1 - P.κ) * P.α)) (rProfit P F))
    (hpr : ∀ p : ℝ, rProfit P F p ≤ rProfit P F pr)
    (hc : P.c < pHatA P lam) :
    ∀ p : ℝ, IsOptimalPrice P F lam p ↔ p = max (pHatA P lam) pr := by sorry

end SunkCost.SmallBias
