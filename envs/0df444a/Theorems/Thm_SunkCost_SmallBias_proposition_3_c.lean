-- Prove2me | Theorems.Thm_SunkCost_SmallBias_proposition_3_c
-- name    : SunkCost.SmallBias.proposition_3_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:51.814086+00:00
-- url     : https://prove2.me/theorems/8c233f49-c801-4de7-9450-d6efebbe7462
-- title:
--   Proposition 3(c), p. 10 (PDF 11) — for λ < λ1, firm profits, consumer welfare and social welfare are weakly increasing in λ
-- statement:
--   Let the standing assumptions hold, let $F$ be a valuation distribution with support $(0,1)$, let the objective $(p-c)(1-F(v_3))$ of (7) be strictly concave on $[0,(1-\kappa)\alpha]$ with maximizer $p_r$, assume $c<\hat p_a(\lambda)$ for every $\lambda\in(0,\lambda_1)$, and assume
--
--   $$p_r<\frac{\kappa\alpha(1-\beta)}{\beta}.$$
--
--   Let $0\le\lambda\le\lambda'<\lambda_1$ (the comparison includes the unbiased case $\lambda=0$), let $p$ be an optimal price at bias $\lambda$ and $p'$ an optimal price at bias $\lambda'$. Then
--
--   $$\Pi_\lambda(p)\le\Pi_{\lambda'}(p'),\qquad CS_\lambda(p)\le CS_{\lambda'}(p'),\qquad SW_\lambda(p)\le SW_{\lambda'}(p'),$$
--
--   where $\Pi$ is the firm's profit, $CS$ is consumer welfare (the $F$-integral over the buyers of their long-run utility (2)/(3)) and $SW=CS+\Pi$ is social welfare.
--
--   This is the paper's win–win result: when the bias is small, sunk-cost bias counteracts the consumers' self-control problem, raises consumption, and benefits the firm, the consumers and society at the same time.
--
--   **Formalization Note.** Optimal prices are quantified, not substituted: any optimal price at each bias will do. Demand is the measure of the primitive buyer set. Welfare uses long-run preferences ($\beta=1$) at the actual usage and, like (2), omits the discomfort $-\lambda p$; social welfare is read as consumer welfare plus profit. The assumption $c<\hat p_a$ of p. 10 depends on $\lambda$ and is required on the whole range $(0,\lambda_1)$. At $\beta=1$ the hypothesis on $p_r$ cannot hold, as on the page.
-- source:
--   Jain and Chen, Sunk cost bias and time inconsistency: a strategic analysis of pricing decisions, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4479, p. 10 (PDF 11), Proposition 3(c), with the assumptions of §4.2 (p. 10: welfare at β = 1, strict concavity of (7), c < p̂a)

import Mathlib
import Definitions.Def_SunkCost_SmallBias_Model

namespace SunkCost.SmallBias

/-- Proposition 3(c), p. 10 (PDF 11): if `p_r < κα(1 − β)/β` (and the standing assumptions of
§4.2 hold on `(0, λ₁)`), then for `0 ≤ λ ≤ λ' < λ₁` the firm's profit, consumer welfare and
social welfare at an optimal price for `λ` are at most those at an optimal price for `λ'`. -/
theorem proposition_3_c (P : Params) (hS : P.Standing) (F : StieltjesFunction ℝ)
    (hF : ValuationCDF F) (pr : ℝ)
    (hconc : StrictConcaveOn ℝ (Set.Icc 0 ((1 - P.κ) * P.α)) (rProfit P F))
    (hpr : ∀ p : ℝ, rProfit P F p ≤ rProfit P F pr)
    (hpr_lt : pr < P.κ * P.α * (1 - P.β) / P.β)
    (hc : ∀ l ∈ Set.Ioo 0 (lam1 P), P.c < pHatA P l)
    (l l' : ℝ) (hl : l ∈ Set.Ico 0 (lam1 P)) (hl' : l' ∈ Set.Ico 0 (lam1 P)) (hll' : l ≤ l')
    (p p' : ℝ) (hp : IsOptimalPrice P F l p) (hp' : IsOptimalPrice P F l' p') :
    profit P F l p ≤ profit P F l' p' ∧
    consumerWelfare P F l p ≤ consumerWelfare P F l' p' ∧
    socialWelfare P F l p ≤ socialWelfare P F l' p' := by sorry

end SunkCost.SmallBias
