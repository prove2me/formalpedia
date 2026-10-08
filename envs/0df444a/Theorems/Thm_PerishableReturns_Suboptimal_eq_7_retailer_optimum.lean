-- Prove2me | Theorems.Thm_PerishableReturns_Suboptimal_eq_7_retailer_optimum
-- name    : PerishableReturns.Suboptimal.eq_7_retailer_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:56.912706+00:00
-- url     : https://prove2.me/theorems/2e00ebc0-153c-4192-877f-87cbfb105532
-- title:
--   (7): the retailer's optimal-order condition
-- statement:
--   Under an admissible wholesale price $c_1$, return credit $c_2$ and return fraction $R$, let $EP_R$ be the retailer's expected profit in (6). Let demand have continuous CDF $F$, support in $[0,\infty)$ and finite mean. An order $Q$ maximizes retailer profit over nonnegative orders exactly when $Q\ge0$ and
--
--   $$0=-c_1+p+g-F(Q)(p+g-c_2)-F((1-R)Q)(1-R)(c_2-c_3).$$
--
--   This condition identifies all retailer-optimal orders, including intervals of optima when the CDF is flat, and is the comparison point for the integrated channel condition (5).
--
--   **Formalization Note** Admissibility means $c_3<c<c_1<p$, $c_3<c_2\le c_1$, and $0\le R\le1$; $g,g_1\ge0$ are cost conventions. Demand is a finite-mean probability law rather than an explicit density, and atomlessness is assumed where the paper uses its density. The printed second derivative following (7) has $f(Q)$ in its second term; differentiation of $F((1-R)Q)$ gives $f((1-R)Q)$ there. The displayed first order equation above is unchanged.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), (7), p. 170

import Mathlib
import Definitions.Def_PerishableReturns_Suboptimal_Model

namespace PerishableReturns.Suboptimal

open MeasureTheory ProbabilityTheory

/-- (7), p. 170: the retailer's optimal-order condition under an admissible return policy. -/
theorem eq_7_retailer_optimum (K : Costs) (c1 c2 R : ℝ)
    (hpolicy : K.Admissible c1 c2 R) (D : Measure ℝ) (hD : IsDemand D)
    [NullSingletonClass D] :
    ∀ Q : ℝ, IsOptimalOrder (EPR K c1 c2 R D) Q ↔
      0 ≤ Q ∧
      0 = -c1 + K.p + K.g - cdf D Q * (K.p + K.g - c2) -
        cdf D ((1 - R) * Q) * ((1 - R) * (c2 - K.c3)) := by sorry

end PerishableReturns.Suboptimal
