-- Prove2me | Theorems.Thm_PerishableReturns_Suboptimal_appendix_theorem_2_no_returns
-- name    : PerishableReturns.Suboptimal.appendix_theorem_2_no_returns
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:28:40.293+00:00
-- url     : https://prove2.me/theorems/097756e3-a318-45ec-9908-d60f810d5c76
-- title:
--   Appendix, Theorem 2: the no-return wholesale price
-- statement:
--   Suppose $c_3<c<c_1<p$, and $g,g_1\ge0$. With no returns ($R=0$), equations (9)–(10) reduce to an equality that holds if and only if the wholesale price is
--
--   $$c_1=c-\frac{g_1(c-c_3)}{p+g_2-c_3}.$$
--
--   The right side is at most $c$, so under $c_1>c$ the reduced equation
--   $$0=c_1-p-g+\frac{(p+g_2-c)(p+g-c_3)}{p+g_2-c_3}$$
--   fails. The statement asserts both the equivalence and this failure, as the proof of Theorem 2 does.
--
--   **Formalization Note** When $R=0$, the credit $c_2$ does not affect the retailer's profit or this equation. The denominator is positive because $p>c>c_3$ and $g_2\ge0$. The paper does not state $g_1\ge0$ separately, but calls it a goodwill cost; this sign is necessary for the ensuing contradiction.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), Appendix, proof of Theorem 2, p. 175

import Mathlib
import Definitions.Def_PerishableReturns_Suboptimal_Model

namespace PerishableReturns.Suboptimal

/-- Appendix, proof of Theorem 2, p. 175: at `R = 0`, (9)–(10) is equivalent to
`c1 = c − g1(c − c3)/(p + g2 − c3)`, and this contradicts `c1 > c`. -/
theorem appendix_theorem_2_no_returns (K : Costs) (c1 : ℝ)
    (hc : K.c < c1) (hp : c1 < K.p) :
    ((0 = (c1 - K.p - K.g) +
      (K.p + K.g2 - K.c) * (K.p + K.g - K.c3) / (K.p + K.g2 - K.c3)) ↔
      c1 = K.c - K.g1 * (K.c - K.c3) / (K.p + K.g2 - K.c3)) ∧
    0 ≠ (c1 - K.p - K.g) +
      (K.p + K.g2 - K.c) * (K.p + K.g - K.c3) / (K.p + K.g2 - K.c3) := by sorry

end PerishableReturns.Suboptimal
