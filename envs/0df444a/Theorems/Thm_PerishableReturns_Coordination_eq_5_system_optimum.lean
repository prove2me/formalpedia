-- Prove2me | Theorems.Thm_PerishableReturns_Coordination_eq_5_system_optimum
-- name    : PerishableReturns.Coordination.eq_5_system_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:28:47.563766+00:00
-- url     : https://prove2.me/theorems/53e97f40-f90c-4544-ae93-ac5163b8e5a3
-- title:
--   (4)–(5) — the company store's optimal orders are the Q ≥ 0 with F(Q) = (p + g2 − c)/(p + g2 − c3)
-- statement:
--   Consider the company store of Pasternack's model: the manufacturer sells directly, with production cost $c$, salvage value $c_3$, price $p$ and total goodwill cost $g_2 = g + g_1$, where $c_3 < c < p$ and $g, g_1 \ge 0$. Let demand have a continuous distribution function $F$ on $[0,\infty)$ with finite mean, and let $EP_T(Q)$ be the expected profit (3).
--
--   Then an optimal production quantity exists, and a quantity $Q^*_T$ is optimal (maximizes $EP_T$ over $Q \ge 0$) if and only if $Q^*_T \ge 0$ and
--   $$F(Q^*_T) = \frac{p + g_2 - c}{p + g_2 - c_3}.$$
--
--   This is the critical-fractile characterization of the integrated system's optimum, equations (4)–(5) of the paper. It identifies the order quantity a coordinating policy must induce, and its existence part guarantees that the coordination statements of the mission are not vacuous.
--
--   **Formalization Note.** The paper obtains (5) from the first-order condition (4) and observes that it is a global maximum; it presupposes that the optimum $Q^*_T$ exists, and this statement makes that existence explicit. Demand is a probability measure on $[0,\infty)$ with finite mean and no atoms (the paper's density). The denominator $p + g_2 - c_3$ is positive because $c_3 < c < p$ and $g_2 \ge 0$, so the division is genuine. Optimality is over order quantities $Q \ge 0$.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), (4)–(5), p. 170

import Mathlib
import Definitions.Def_PerishableReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

namespace PerishableReturns.Coordination

theorem eq_5_system_optimum (K : Costs) (D : Measure ℝ) (hD : IsDemand D) [NullSingletonClass D] :
    (∃ Q : ℝ, IsOptimalOrder (EPT K D) Q) ∧
    ∀ Q : ℝ, IsOptimalOrder (EPT K D) Q ↔
      0 ≤ Q ∧ cdf D Q = (K.p + K.g2 - K.c) / (K.p + K.g2 - K.c3) := by sorry

end PerishableReturns.Coordination
