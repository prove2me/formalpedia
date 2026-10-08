-- Prove2me | Theorems.Thm_PerishableReturns_Coordination_theorem_3_credit_range
-- name    : PerishableReturns.Coordination.theorem_3_credit_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:21.615448+00:00
-- url     : https://prove2.me/theorems/0eb67e7f-6ee1-4e5b-a168-07a420953ab7
-- title:
--   Appendix, proof of Theorem 3 — for c < c1 < p a credit c2 satisfying (11) exists with c3 < c2 < c1
-- statement:
--   In Pasternack's model, with cost data $c_3 < c < p$ and goodwill costs $g, g_1 \ge 0$ ($g_2 = g + g_1$), let the retailer's price $c_1$ satisfy $c < c_1 < p$. Then there is a return credit $c_2$ satisfying relationship (11),
--   $$c_1 = (p + g) - \frac{(p + g_2 - c)(p + g - c_2)}{p + g_2 - c_3},$$
--   such that
--   $$c_3 < c_2 < c_1.$$
--
--   This is what the paper's Appendix states must be shown to prove Theorem 3: for every admissible price $c_1$ the coordinating credit is a genuine partial credit, strictly between the salvage value and the price.
--
--   The printed argument for $c_3 < c_2$ establishes only $p + g_2 - c_3 > p + g - c_2$, that is $c_2 > c_3 - g_1$, which gives $c_3 < c_2$ only when $g_1 = 0$; the claim itself holds for every $g_1 \ge 0$, and that claim is what is stated here.
--
--   **Formalization Note.** The nonnegativity of $g$ and $g_1$ is implicit in the paper (they are costs) and is a field of the cost data. The denominator $p + g_2 - c_3$ is positive.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), Appendix, proof of Theorem 3, p. 175

import Mathlib
import Definitions.Def_PerishableReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace PerishableReturns.Coordination

theorem theorem_3_credit_range (K : Costs) (c1 : ℝ) (hc : K.c < c1) (hp : c1 < K.p) :
    ∃ c2 : ℝ,
      c1 = (K.p + K.g) - (K.p + K.g2 - K.c) * (K.p + K.g - c2) / (K.p + K.g2 - K.c3) ∧
      K.c3 < c2 ∧ c2 < c1 := by sorry

end PerishableReturns.Coordination
