-- Prove2me | Theorems.Thm_PerishBaseStock_Lifetime_eq_5_heuristic_bounds
-- name    : PerishBaseStock.Lifetime.eq_5_heuristic_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:48.43377+00:00
-- url     : https://prove2.me/theorems/a6f20d20-1349-4cf8-97bc-0c195b82b0ab
-- title:
--   (5) — $F^{-1}(\frac{p}{p+h+\theta})\le\widetilde S\le F^{-1}(\frac{p}{p+h})$
-- statement:
--   Let $\widetilde C$ be the heuristic cost (4) of the perishable inventory system with lifetime $m\ge 1$, costs $h>0$, $p>0$, $\theta\ge 0$, and let $F^{-1}(x)=\inf\{y:F(y)\ge x\}$ be the generalized inverse of the demand distribution function. Then:
--
--   1. every minimizer $\widetilde S$ of $\widetilde C$ over $[0,+\infty)$ satisfies
--   $$F^{-1}\Big(\frac{p}{p+h+\theta}\Big)\le\widetilde S;$$
--   2. $\widetilde C$ has a least minimizer $\widetilde S$ over $[0,+\infty)$, and it satisfies
--   $$\widetilde S\le F^{-1}\Big(\frac{p}{p+h}\Big)=S^{NP}.$$
--
--   These bounds locate the heuristic level between two newsvendor quantiles, which is what makes it computable by a one-dimensional search, and the upper bound is used in the proof of Theorem 1.
--
--   **Formalization Note** $\widetilde C$ can be constant on an interval to the right of $S^{NP}$ (where $F=p/(p+h)$ and $\sum_{i\le m}D_i$ has no mass), so a minimizer other than the least one may exceed $S^{NP}$; the upper bound of (5) is therefore stated for the least minimizer and the lower bound for every minimizer. Part 2 also asserts that a minimizer exists. $F^{-1}(p/(p+h+\theta))$ is `newsvendorLevel P.law (h + θ) p`.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 10, display (5)

import Definitions.Def_PerishBaseStock_Lifetime_Model
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifetime

theorem eq_5_heuristic_bounds (P : CappedBaseStock.DemandLaw) (c : Params) :
    (∀ Stilde : ℝ≥0, IsHeuristicLevel P c Stilde →
        LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law (c.h + c.θ) c.p ≤ Stilde) ∧
      ∃ S₀ : ℝ≥0, IsHeuristicLevel P c S₀ ∧
        (∀ Stilde : ℝ≥0, IsHeuristicLevel P c Stilde → S₀ ≤ Stilde) ∧
        S₀ ≤ newsvendorNP P c := by sorry

end PerishBaseStock.Lifetime
