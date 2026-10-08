-- Prove2me | Theorems.Thm_PerishableReturns_Coordination_eq_10_coordination_criterion
-- name    : PerishableReturns.Coordination.eq_10_coordination_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:06.516338+00:00
-- url     : https://prove2.me/theorems/8cfee39c-58a5-4898-a387-4673aa150730
-- title:
--   (9)–(10) — an admissible policy coordinates the channel iff (10) holds at every system-optimal order
-- statement:
--   In Pasternack's model, let $(c_1, c_2, R)$ be an admissible policy ($c < c_1 < p$, $c_3 < c_2 \le c_1$, $0 \le R \le 1$), and let demand have a continuous distribution function $F$ on $[0,\infty)$ with finite mean. The channel is coordinated when the retailer's optimal orders for its expected profit (6) are exactly the company store's optimal orders for (3).
--
--   Then the channel is coordinated if and only if, for every $Q^* \ge 0$ satisfying (9),
--   $$F(Q^*) = \frac{p + g_2 - c}{p + g_2 - c_3},$$
--   the policy satisfies (10):
--   $$0 = (c_1 - p - g) + \frac{(p + g_2 - c)(p + g - c_2)}{p + g_2 - c_3} + F((1-R)Q^*)\,[(1-R)(c_2 - c_3)].$$
--
--   The paper obtains (10) by substituting (9) into the retailer's first-order condition (7), and concludes that if the manufacturer chooses $c_1, c_2, R$ so that (10) holds, the retailer orders the system-optimal quantity. This is the general coordination criterion from which Theorems 1–3 are derived.
--
--   **Formalization Note.** The paper states the sufficiency direction in words and obtains (10) as a necessary condition by substitution; the statement records both directions as one equivalence. Coordination is equality of the sets of optimal orders. Demand is a probability measure on $[0,\infty)$ with finite mean and no atoms. The denominator $p + g_2 - c_3$ is positive.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), (9)–(10) and the paragraph after (10), p. 171

import Mathlib
import Definitions.Def_PerishableReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace PerishableReturns.Coordination

theorem eq_10_coordination_criterion (K : Costs) (c1 c2 R : ℝ) (hadm : K.Admissible c1 c2 R)
    (D : Measure ℝ) (hD : IsDemand D) [NullSingletonClass D] :
    Coordinates K c1 c2 R D ↔
      ∀ Q : ℝ, 0 ≤ Q → cdf D Q = (K.p + K.g2 - K.c) / (K.p + K.g2 - K.c3) →
        0 = (c1 - K.p - K.g) + (K.p + K.g2 - K.c) * (K.p + K.g - c2) / (K.p + K.g2 - K.c3)
              + cdf D ((1 - R) * Q) * ((1 - R) * (c2 - K.c3)) := by sorry

end PerishableReturns.Coordination
