-- Prove2me | Theorems.Thm_PerishableReturns_Coordination_eq_11_full_returns
-- name    : PerishableReturns.Coordination.eq_11_full_returns
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:39.464926+00:00
-- url     : https://prove2.me/theorems/728ce574-5340-4486-8487-82049eeeab20
-- title:
--   (11) — with unlimited returns at partial credit, coordination holds iff c1 = (p + g) − (p + g2 − c)(p + g − c2)/(p + g2 − c3)
-- statement:
--   In Pasternack's model, suppose the manufacturer permits unlimited returns ($R = 1$) at partial credit: $c < c_1 < p$ and $c_3 < c_2 < c_1$. Let demand have a continuous distribution function on $[0,\infty)$ with finite mean.
--
--   Then the channel is coordinated (the retailer's optimal orders coincide with the company store's) if and only if
--   $$c_1 = (p + g) - \frac{(p + g_2 - c)(p + g - c_2)}{p + g_2 - c_3}.$$
--
--   This is relationship (11) of the paper. The condition involves only the cost data, not the demand distribution, which is what lets one pricing and return policy coordinate retailers with different demand.
--
--   **Formalization Note.** The paper says (11) "must hold in order to achieve channel coordination" (the forward direction); the reverse direction is the paper's sufficiency statement after (10), specialized to $R = 1$. Both are recorded as one equivalence. Demand is a probability measure on $[0,\infty)$ with finite mean and no atoms. Coordination is equality of the sets of optimal orders.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), (11), p. 171

import Mathlib
import Definitions.Def_PerishableReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace PerishableReturns.Coordination

theorem eq_11_full_returns (K : Costs) (c1 c2 : ℝ) (hadm : K.Admissible c1 c2 1)
    (hpartial : c2 < c1) (D : Measure ℝ) (hD : IsDemand D) [NullSingletonClass D] :
    Coordinates K c1 c2 1 D ↔
      c1 = (K.p + K.g) - (K.p + K.g2 - K.c) * (K.p + K.g - c2) / (K.p + K.g2 - K.c3) := by sorry

end PerishableReturns.Coordination
