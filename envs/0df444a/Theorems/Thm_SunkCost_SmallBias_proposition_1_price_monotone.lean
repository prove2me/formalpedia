-- Prove2me | Theorems.Thm_SunkCost_SmallBias_proposition_1_price_monotone
-- name    : SunkCost.SmallBias.proposition_1_price_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:01.448846+00:00
-- url     : https://prove2.me/theorems/3ac3a101-4c4d-489e-8711-2520dc5e7658
-- title:
--   Proposition 1, p. 8 (PDF 9) — for λ < λ1, demand increases in price below p̂a and decreases above
-- statement:
--   Let the standing assumptions hold, let $F$ be a valuation distribution with support $(0,1)$, and let $0\le\lambda<\lambda_1$. Then:
--
--   1. if $\lambda>0$, the demand $D$ is strictly increasing in $p$ on $[0,\hat p_a]$;
--   2. $D$ is strictly decreasing on $[\hat p_a,(1-\kappa)\alpha]$;
--   3. $D$ is nonincreasing on $[\hat p_a,\infty)$.
--
--   In particular, for $0<\lambda<\lambda_1$,
--
--   $$0\le p<q\le\hat p_a\ \Longrightarrow\ D(p)<D(q).$$
--
--   This is the upward-sloping demand of the paper: a higher price raises the sunk-cost discomfort of leaving the product unused and therefore the share of consumers who would use it, which raises their willingness to buy.
--
--   **Formalization Note.** At $\lambda=0$ the threshold $v_1$ does not depend on the price and demand is flat on $[0,\hat p_a]$, so the strict increase is stated for $\lambda>0$. "Decreases otherwise" is stated strictly up to $(1-\kappa)\alpha$, where demand reaches $0$, and weakly beyond.
-- source:
--   Jain and Chen, Sunk cost bias and time inconsistency: a strategic analysis of pricing decisions, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4479, p. 8 (PDF 9), Proposition 1 ('Demand increases in price for p < p̂a and decreases otherwise.')

import Mathlib
import Definitions.Def_SunkCost_SmallBias_Model

namespace SunkCost.SmallBias

/-- Proposition 1, p. 8 (PDF 9), monotonicity in price: for `0 ≤ λ < λ₁`, demand is strictly
increasing in `p` on `[0, p̂_a]` (when `λ > 0`), strictly decreasing on `[p̂_a, (1 − κ)α]`,
and nonincreasing on `[p̂_a, ∞)`. -/
theorem proposition_1_price_monotone (P : Params) (hS : P.Standing) (F : StieltjesFunction ℝ)
    (hF : ValuationCDF F) (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < lam1 P) :
    (0 < lam → StrictMonoOn (demand P F lam) (Set.Icc 0 (pHatA P lam))) ∧
    StrictAntiOn (demand P F lam) (Set.Icc (pHatA P lam) ((1 - P.κ) * P.α)) ∧
    AntitoneOn (demand P F lam) (Set.Ici (pHatA P lam)) := by sorry

end SunkCost.SmallBias
