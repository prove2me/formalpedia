-- Prove2me | Theorems.Thm_PerishableReturns_Coordination_eq_7_retailer_optimum
-- name    : PerishableReturns.Coordination.eq_7_retailer_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:00.953013+00:00
-- url     : https://prove2.me/theorems/94dc60f6-71e4-4e83-9527-6e5c0df0a880
-- title:
--   (7) — the retailer's optimal orders under an admissible return policy (c1, c2, R)
-- statement:
--   In Pasternack's model, let the manufacturer's policy $(c_1, c_2, R)$ be admissible: $c < c_1 < p$, $c_3 < c_2 \le c_1$, and $0 \le R \le 1$, where the retailer pays $c_1$ per unit and may return up to the fraction $R$ of its order for a credit $c_2$ per unit. Let demand have a continuous distribution function $F$ on $[0,\infty)$ with finite mean, and let $EP_R(Q)$ be the retailer's expected profit (6), with retailer goodwill cost $g \ge 0$.
--
--   Then $Q^*$ is an optimal order for the retailer (maximizes $EP_R$ over $Q \ge 0$) if and only if $Q^* \ge 0$ and
--   $$0 = -c_1 + p + g - F(Q^*)\,[p + g - c_2] - F((1-R)Q^*)\,[(1-R)(c_2 - c_3)].$$
--
--   This is equation (7) of the paper, the retailer's first-order condition, which the paper shows is a global maximum. Comparing it with the system condition (5) yields the coordination criteria (10) and (11).
--
--   **Formalization Note.** Demand is a probability measure on $[0,\infty)$ with finite mean and no atoms (the paper's density). The paper's second-derivative display justifying the global maximum prints $f(Q)$ in its second term where $f((1-R)Q)$ is meant; this does not affect (7). Optimality is over order quantities $Q \ge 0$.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), (7), p. 170

import Mathlib
import Definitions.Def_PerishableReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace PerishableReturns.Coordination

theorem eq_7_retailer_optimum (K : Costs) (c1 c2 R : ℝ) (hadm : K.Admissible c1 c2 R)
    (D : Measure ℝ) (hD : IsDemand D) [NullSingletonClass D] (Q : ℝ) :
    IsOptimalOrder (EPR K c1 c2 R D) Q ↔
      0 ≤ Q ∧ 0 = -c1 + K.p + K.g - cdf D Q * (K.p + K.g - c2)
                - cdf D ((1 - R) * Q) * ((1 - R) * (c2 - K.c3)) := by sorry

end PerishableReturns.Coordination
