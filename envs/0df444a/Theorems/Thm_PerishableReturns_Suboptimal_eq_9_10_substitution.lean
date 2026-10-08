-- Prove2me | Theorems.Thm_PerishableReturns_Suboptimal_eq_9_10_substitution
-- name    : PerishableReturns.Suboptimal.eq_9_10_substitution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:57.917797+00:00
-- url     : https://prove2.me/theorems/f1f4d3b9-6481-4626-a758-bc07d474d858
-- title:
--   (9)–(10): substituting the channel-optimal fractile
-- statement:
--   Let the costs and policy be admissible, and let demand have continuous CDF $F$, nonnegative support and finite mean. Fix an order quantity $Q$ satisfying the integrated company's condition (9),
--
--   $$F(Q)=\frac{p+g_2-c}{p+g_2-c_3}.$$
--
--   Then the retailer's equation (7) at $Q$ holds if and only if equation (10) holds at $Q$:
--
--   $$0=(c_1-p-g)+\frac{(p+g_2-c)(p+g-c_2)}{p+g_2-c_3}+F((1-R)Q)(1-R)(c_2-c_3).$$
--
--   This algebraic comparison states the paper's common condition for a system-optimal order to be retailer-optimal.
--
--   **Formalization Note** $Q$ is fixed by (9), not quantified as an arbitrary retailer optimum. The probability measure representation, finite-mean support condition, atomlessness and nonnegative goodwill costs follow the model conventions. The denominator is positive under $c_3<c<p$ and $g_2\ge0$.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), (9)–(10), p. 171

import Mathlib
import Definitions.Def_PerishableReturns_Suboptimal_Model

namespace PerishableReturns.Suboptimal

open MeasureTheory ProbabilityTheory

/-- (9) substituted into (7) gives (10), p. 171. -/
theorem eq_9_10_substitution (K : Costs) (c1 c2 R : ℝ)
    (hpolicy : K.Admissible c1 c2 R) (D : Measure ℝ) (hD : IsDemand D)
    [NullSingletonClass D] (Q : ℝ)
    (hQ : cdf D Q = (K.p + K.g2 - K.c) / (K.p + K.g2 - K.c3)) :
    (0 = -c1 + K.p + K.g - cdf D Q * (K.p + K.g - c2) -
      cdf D ((1 - R) * Q) * ((1 - R) * (c2 - K.c3))) ↔
    (0 = (c1 - K.p - K.g) +
      (K.p + K.g2 - K.c) * (K.p + K.g - c2) / (K.p + K.g2 - K.c3) +
      cdf D ((1 - R) * Q) * ((1 - R) * (c2 - K.c3))) := by sorry

end PerishableReturns.Suboptimal
