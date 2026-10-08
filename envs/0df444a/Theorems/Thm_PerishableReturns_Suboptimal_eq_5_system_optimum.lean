-- Prove2me | Theorems.Thm_PerishableReturns_Suboptimal_eq_5_system_optimum
-- name    : PerishableReturns.Suboptimal.eq_5_system_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:28:00.346363+00:00
-- url     : https://prove2.me/theorems/0347a860-f21f-48a4-b0a7-31fdd70f3d5d
-- title:
--   (4)–(5): the integrated company's optimal order quantity
-- statement:
--   Let $c_3<c<p$ be the salvage value, manufacturing cost and selling price, and let $g_2=g+g_1$ be the total nonnegative stockout goodwill cost. Let demand have a continuous distribution function $F$, be supported on $[0,\infty)$, and have finite mean. For the company-store profit $EP_T$ in (3), a nonnegative optimal order exists, and every order quantity $Q$ satisfies
--
--   $$Q\in\operatorname*{arg\,max}_{q\ge0}EP_T(q)\quad\Longleftrightarrow\quad Q\ge0\ \text{and}\ F(Q)=\frac{p+g_2-c}{p+g_2-c_3}.$$
--
--   This is the integrated channel's benchmark order condition used in both suboptimality claims.
--
--   **Formalization Note** The law is represented as a probability measure on $[0,\infty)$ with finite mean. Atomlessness expresses the paper's density assumption for this result; the CDF need not be strictly increasing. The denominator is positive because $p>c>c_3$ and $g_2\ge0$.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), (4)–(5), p. 170

import Mathlib
import Definitions.Def_PerishableReturns_Suboptimal_Model

namespace PerishableReturns.Suboptimal

open MeasureTheory ProbabilityTheory

/-- (4)–(5), p. 170: the integrated channel's optimal-order fractile. -/
theorem eq_5_system_optimum (K : Costs) (D : Measure ℝ) (hD : IsDemand D)
    [NullSingletonClass D] :
    (∃ Q : ℝ, IsOptimalOrder (EPT K D) Q) ∧
    (∀ Q : ℝ, IsOptimalOrder (EPT K D) Q ↔
      0 ≤ Q ∧ cdf D Q = (K.p + K.g2 - K.c) / (K.p + K.g2 - K.c3)) := by sorry

end PerishableReturns.Suboptimal
