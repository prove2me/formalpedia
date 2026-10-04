-- Prove2me | Theorems.Thm_PricingRM_DetHeuristic_single_price_ratio
-- name    : PricingRM.DetHeuristic.single_price_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:34:12.706075+00:00
-- url     : https://prove2.me/theorems/cfe9ed03-ab50-4a85-93f1-7c954a9db51e
-- title:
--   Proposition 6, eq. (26) — the deterministic price loses at most $\nu^{\det}/2$ in the single-price model
-- statement:
--   Consider the single-price model: one period, capacity $C$, nonnegative random demand $D(p)$ with finite mean at each price $p \ge 0$, and optimal expected revenue $V(C) = \sup_{p \ge 0} E[p\min\{D(p), C\}]$. Let $p^{\det} \ge 0$ be an optimal deterministic price, i.e.
--   $$
--   p\min\{E[D(p)], C\} \le p^{\det}\min\{E[D(p^{\det})], C\} \quad \text{for all } p \ge 0,
--   $$
--   with $E[D(p^{\det})] \le C$. Assume $D(p^{\det})$ has finite variance, let $\nu^{\det} = \sqrt{\operatorname{Var} D(p^{\det})}/E[D(p^{\det})]$ be its coefficient of variation, and assume $V(C) > 0$. Then the expected revenue $V(C, p^{\det}) = p^{\det} E\big[D(p^{\det}) - (D(p^{\det}) - C)^+\big]$ of charging $p^{\det}$ satisfies
--   $$
--   \frac{V(C, p^{\det})}{V(C)} \ge 1 - \frac{\nu^{\det}}{2}.
--   $$
--
--   The relative loss of the fixed deterministic price is governed by the coefficient of variation of demand, not its variance. Proposition 8 extends this to $N$ periods.
--
--   **Formalization Note** The single-period model is `PricingModel 1`. The paper takes $p^{\det}$ from its Proposition 1, which yields a maximizer of $p\min\{E[D(p)], C\}$ with $E[D(p^{\det})] \le C$; both properties are hypotheses here. The paper divides by $V(C)$ and $E[D(p^{\det})]$ without comment; $V(C) > 0$ is assumed, and it implies $E[D(p^{\det})] > 0$.
-- source:
--   Bitran and Caldentey, An Overview of Pricing Models for Revenue Management, MSOM 5(3) 2003, p. 218, Proposition 6, eq. (26); setup and eq. (25) on pp. 217–218

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PricingRM.DetHeuristic

/-- Bitran–Caldentey (2003), Proposition 6, eq. (26), p. 218: in a single-period model, let
`pdet ≥ 0` maximize `p·min{E[D(p)], C}` over `p ≥ 0`, with `E[D(pdet)] ≤ C`, and let
`ν = √(Var D(pdet)) / E[D(pdet)]`. If the optimal expected revenue `V(C)` is positive, then
`V(C, pdet) / V(C) ≥ 1 - ν/2`, where `V(C, pdet) = pdet·E[D(pdet) - (D(pdet) - C)^+]`. -/
theorem single_price_ratio (M : PricingModel 1) (C pdet : ℝ) (hp : 0 ≤ pdet)
    (hopt : ∀ p : ℝ, 0 ≤ p → p * min (meanDemand M 0 p) C ≤ pdet * min (meanDemand M 0 pdet) C)
    (hcap : meanDemand M 0 pdet ≤ C)
    (hL2 : MemLp (fun x : ℝ => x) 2 (M.μ 0 pdet))
    (hV : 0 < optValue M C) :
    (pdet * ∫ x, (x - max (x - C) 0) ∂(M.μ 0 pdet)) / (optValue M C).toReal ≥
      1 - (Real.sqrt (variance (fun x : ℝ => x) (M.μ 0 pdet)) /
        meanDemand M 0 pdet) / 2 := by sorry

end PricingRM.DetHeuristic
