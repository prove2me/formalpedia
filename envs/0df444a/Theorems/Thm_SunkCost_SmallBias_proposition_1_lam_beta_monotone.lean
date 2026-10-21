-- Prove2me | Theorems.Thm_SunkCost_SmallBias_proposition_1_lam_beta_monotone
-- name    : SunkCost.SmallBias.proposition_1_lam_beta_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:50.991074+00:00
-- url     : https://prove2.me/theorems/58311189-1317-47f9-8646-11b98df6607b
-- title:
--   Proposition 1, p. 8 (PDF 9) — for λ < λ1, demand weakly increases in λ and β
-- statement:
--   Let the standing assumptions hold, let $F$ be a valuation distribution with support $(0,1)$, and fix a price $p\ge 0$.
--
--   1. The map $\lambda\mapsto D_\lambda(p)$ is nondecreasing on $[0,\lambda_1)$.
--   2. Let $\beta\le\beta'$, with all other parameters equal and both parameter sets satisfying the standing assumptions. If $0\le\lambda<\lambda_1(\beta')$, then
--
--   $$D_{\lambda,\beta}(p)\le D_{\lambda,\beta'}(p).$$
--
--   A stronger sunk-cost bias and a weaker present bias both make more consumers use, and hence buy, the product.
--
--   **Formalization Note.** Since $\lambda_1=(1-\beta)/(\alpha(1-\kappa))$ decreases in $\beta$, the hypothesis $\lambda<\lambda_1(\beta')$ places both parameter sets in the regime of Proposition 1.
-- source:
--   Jain and Chen, Sunk cost bias and time inconsistency: a strategic analysis of pricing decisions, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4479, p. 8 (PDF 9), Proposition 1 ('Furthermore, demand weakly increases in λ and β.')

import Mathlib
import Definitions.Def_SunkCost_SmallBias_Model

namespace SunkCost.SmallBias

/-- Proposition 1, p. 8 (PDF 9), monotonicity in `λ` and `β`: at every price `p ≥ 0`,
demand is nondecreasing in `λ` on `[0, λ₁)`; and raising `β` (all other parameters fixed,
both parameter sets standing, `0 ≤ λ < λ₁` for the larger `β`) does not decrease demand. -/
theorem proposition_1_lam_beta_monotone (P : Params) (hS : P.Standing)
    (F : StieltjesFunction ℝ) (hF : ValuationCDF F) (p : ℝ) (hp : 0 ≤ p) :
    MonotoneOn (fun l => demand P F l p) (Set.Ico 0 (lam1 P)) ∧
    ∀ P' : Params, P'.Standing → P'.α = P.α → P'.κ = P.κ → P'.c = P.c → P.β ≤ P'.β →
      ∀ lam : ℝ, 0 ≤ lam → lam < lam1 P' → demand P F lam p ≤ demand P' F lam p := by sorry

end SunkCost.SmallBias
