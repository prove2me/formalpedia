-- Prove2me | Theorems.Thm_SunkCost_SmallBias_proposition_1_demand
-- name    : SunkCost.SmallBias.proposition_1_demand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:48.793261+00:00
-- url     : https://prove2.me/theorems/7bb6e486-1abc-424b-a27f-b4a7b553a602
-- title:
--   Proposition 1, p. 8 (PDF 9) — for λ < (1−β)/(α(1−κ)), demand is 1−F(v1), then 1−F(v3), then 0
-- statement:
--   Let the standing assumptions hold, let $F$ be a valuation distribution with support $(0,1)$, and let $0\le\lambda<\lambda_1=(1-\beta)/(\alpha(1-\kappa))$. Then for every price $p\ge 0$
--
--   $$D(p)=\begin{cases}1-F(v_1) & \text{if } p\le \hat p_a,\\ 1-F(v_3) & \text{if } p\in(\hat p_a,(1-\kappa)\alpha),\\ 0 & \text{if } p\ge(1-\kappa)\alpha,\end{cases}\qquad \hat p_a=\frac{\kappa(1-\beta)\alpha}{\lambda\alpha+\beta}.$$
--
--   For a small sunk-cost bias no consumer overconsumes, and the demand has a kink at $\hat p_a$, where the usage constraint $v\ge v_1$ stops binding and the purchase constraint $v>v_3$ takes over. This formula (5) is what the firm optimizes in §4.2.
--
--   **Formalization Note.** The bias $\lambda$ is nonnegative, as the discomfort $-\lambda p$ requires, and prices are nonnegative.
-- source:
--   Jain and Chen, Sunk cost bias and time inconsistency: a strategic analysis of pricing decisions, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4479, p. 8 (PDF 9), Proposition 1, formula (5)

import Mathlib
import Definitions.Def_SunkCost_SmallBias_Model

namespace SunkCost.SmallBias

/-- Proposition 1, formula (5), p. 8 (PDF 9): if `0 ≤ λ < λ₁ = (1 − β)/(α(1 − κ))`, then for
every price `p ≥ 0` the demand is `1 − F(v₁)` if `p ≤ p̂_a`, `1 − F(v₃)` if
`p̂_a < p < (1 − κ)α`, and `0` if `p ≥ (1 − κ)α`. -/
theorem proposition_1_demand (P : Params) (hS : P.Standing) (F : StieltjesFunction ℝ)
    (hF : ValuationCDF F) (lam p : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < lam1 P) (hp : 0 ≤ p) :
    demand P F lam p =
      if p ≤ pHatA P lam then 1 - F (v1 P lam p)
      else if p < (1 - P.κ) * P.α then 1 - F (v3 P p)
      else 0 := by sorry

end SunkCost.SmallBias
