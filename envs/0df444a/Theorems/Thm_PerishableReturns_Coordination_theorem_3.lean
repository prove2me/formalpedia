-- Prove2me | Theorems.Thm_PerishableReturns_Coordination_theorem_3
-- name    : PerishableReturns.Coordination.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:25.42209+00:00
-- url     : https://prove2.me/theorems/53d18e23-e905-47ff-9814-9e2de3593cdf
-- title:
--   Theorem 3 — unlimited returns at partial credit coordinate the channel for appropriately chosen c1 and c2
-- statement:
--   **Theorem 3** (Pasternack 1985). *A policy which allows for unlimited returns at partial credit will be system optimal for appropriately chosen values of $c_1$ and $c_2$.*
--
--   Precisely: let the cost data satisfy $c_3 < c < p$ and $g, g_1 \ge 0$, with $g_2 = g + g_1$, and let the retailer's price $c_1$ satisfy $c < c_1 < p$. Then there is a return credit $c_2$ with
--   $$c_3 < c_2 < c_1 \qquad\text{and}\qquad c_1 = (p + g) - \frac{(p + g_2 - c)(p + g - c_2)}{p + g_2 - c_3} \quad (11)$$
--   such that, for **every** demand law with a continuous distribution function on $[0,\infty)$ and finite mean, the policy with unlimited returns ($R = 1$) at credit $c_2$ coordinates the channel: the retailer's optimal orders for its expected profit (6) are exactly the company store's optimal orders for (3).
--
--   The credit $c_2$ depends only on the cost data, not on the demand distribution. This is the basis of the paper's conclusion that a single pricing and return policy with full returns at partial credit coordinates a manufacturer's channel even when it sells to several retailers with different demand.
--
--   **Formalization Note.** "Unlimited returns" is $R = 1$ and "partial credit" is $c_2 < c_1$ (p. 171). "System optimal" is the paper's channel coordination (p. 171), read as equality of the retailer's and the company store's sets of optimal orders over $Q \ge 0$. The range $c_3 < c_2 < c_1$ and relationship (11) are part of the conclusion, as in the paper's proof (p. 175). The quantifier over demand laws is inside the existence of $c_2$. Demand laws are probability measures on $[0,\infty)$ with finite mean and no atoms (the paper's density). The nonnegativity of $g, g_1$ is implicit in the paper.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), Theorem 3 and (11), p. 171; Appendix, proof of Theorem 3, p. 175

import Mathlib
import Definitions.Def_PerishableReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace PerishableReturns.Coordination

theorem theorem_3 (K : Costs) (c1 : ℝ) (hc : K.c < c1) (hp : c1 < K.p) :
    ∃ c2 : ℝ, K.c3 < c2 ∧ c2 < c1 ∧
      c1 = (K.p + K.g) - (K.p + K.g2 - K.c) * (K.p + K.g - c2) / (K.p + K.g2 - K.c3) ∧
      ∀ D : Measure ℝ, IsDemand D → NullSingletonClass D → Coordinates K c1 c2 1 D := by sorry

end PerishableReturns.Coordination
