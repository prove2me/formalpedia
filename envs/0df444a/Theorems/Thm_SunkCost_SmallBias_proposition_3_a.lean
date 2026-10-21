-- Prove2me | Theorems.Thm_SunkCost_SmallBias_proposition_3_a
-- name    : SunkCost.SmallBias.proposition_3_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:45.421903+00:00
-- url     : https://prove2.me/theorems/fdeb9561-ecc5-4afc-a0c0-6db96638ade6
-- title:
--   Proposition 3(a), p. 10 (PDF 11) — a threshold λ* with optimal price p̂a below it and pr above it
-- statement:
--   Let the standing assumptions hold, let $F$ be a valuation distribution with support $(0,1)$, let the objective $(p-c)(1-F(v_3))$ of (7) be strictly concave on $[0,(1-\kappa)\alpha]$ with maximizer $p_r$, and assume $c<\hat p_a(\lambda)$ for every $\lambda\in(0,\lambda_1)$. If
--
--   $$p_r<\frac{\kappa\alpha(1-\beta)}{\beta},$$
--
--   then there is a $\lambda^*>0$ such that, for $\lambda\in(0,\lambda_1)$, the unique optimal price is $\hat p_a=\kappa(1-\beta)\alpha/(\lambda\alpha+\beta)$ when $\lambda<\lambda^*$ and $p_r$ when $\lambda>\lambda^*$.
--
--   The optimal price first falls with the bias, along $\hat p_a$, and then stays at the unconstrained price $p_r$; for small $\lambda$ it does not depend on the marginal cost.
--
--   **Formalization Note.** One threshold $\lambda^*$ serves every $\lambda$. It may exceed $\lambda_1$, in which case the second clause is vacuous on $(0,\lambda_1)$. "The optimal prices are $\hat p_a$" is read as: $\hat p_a$ is the unique optimal price. The assumption $c<\hat p_a$ of p. 10 depends on $\lambda$ and is required on the whole range. At $\beta=1$ the hypothesis on $p_r$ cannot hold, as on the page.
-- source:
--   Jain and Chen, Sunk cost bias and time inconsistency: a strategic analysis of pricing decisions, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4479, p. 10 (PDF 11), Proposition 3(a), with the assumptions of §4.2 (p. 10: strict concavity of (7), c < p̂a)

import Mathlib
import Definitions.Def_SunkCost_SmallBias_Model

namespace SunkCost.SmallBias

/-- Proposition 3(a), p. 10 (PDF 11): if `p_r < κα(1 − β)/β` (and the standing assumptions of
§4.2 hold on `(0, λ₁)`), there is one threshold `λ* > 0` such that for `λ ∈ (0, λ₁)` the unique
optimal price is `p̂_a` when `λ < λ*` and `p_r` when `λ > λ*`. -/
theorem proposition_3_a (P : Params) (hS : P.Standing) (F : StieltjesFunction ℝ)
    (hF : ValuationCDF F) (pr : ℝ)
    (hconc : StrictConcaveOn ℝ (Set.Icc 0 ((1 - P.κ) * P.α)) (rProfit P F))
    (hpr : ∀ p : ℝ, rProfit P F p ≤ rProfit P F pr)
    (hpr_lt : pr < P.κ * P.α * (1 - P.β) / P.β)
    (hc : ∀ l ∈ Set.Ioo 0 (lam1 P), P.c < pHatA P l) :
    ∃ lamStar : ℝ, 0 < lamStar ∧ ∀ l ∈ Set.Ioo 0 (lam1 P),
      (l < lamStar → ∀ p : ℝ, IsOptimalPrice P F l p ↔ p = pHatA P l) ∧
      (lamStar < l → ∀ p : ℝ, IsOptimalPrice P F l p ↔ p = pr) := by sorry

end SunkCost.SmallBias
