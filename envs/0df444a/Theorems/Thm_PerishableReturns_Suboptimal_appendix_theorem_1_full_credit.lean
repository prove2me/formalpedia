-- Prove2me | Theorems.Thm_PerishableReturns_Suboptimal_appendix_theorem_1_full_credit
-- name    : PerishableReturns.Suboptimal.appendix_theorem_1_full_credit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:28:18.150244+00:00
-- url     : https://prove2.me/theorems/8f4a9bfa-8f70-4a92-b965-7e8010bb5f2f
-- title:
--   Appendix, Theorem 1: the full-credit equation is impossible
-- statement:
--   Suppose $c_3<c<c_1<p$, and $g,g_1\ge0$. With unlimited returns $R=1$ and full credit $c_2=c_1$, the coordination equation (10) would require
--
--   $$0=(c_1-p-g)+\frac{(p+g_2-c)(p+g-c_1)}{p+g_2-c_3}.$$
--
--   This equality cannot hold. It is the algebraic obstruction behind Theorem 1: an integrated-company optimal order cannot also be retailer-optimal under unlimited full-credit returns.
--
--   **Formalization Note** $p+g-c_1>0$ and $p+g_2-c_3>0$ follow from the stated cost inequalities, so the cancellation in the paper's appendix is legitimate. The statement uses the exact $R=1$, $c_2=c_1$ policy, without a demand-dependent choice.
-- source:
--   Pasternack, Optimal Pricing and Return Policies for Perishable Commodities, Marketing Science 4(2) (1985), Appendix, proof of Theorem 1, p. 175

import Mathlib
import Definitions.Def_PerishableReturns_Suboptimal_Model

namespace PerishableReturns.Suboptimal

/-- Appendix, proof of Theorem 1, p. 175: (10) cannot hold at full credit. -/
theorem appendix_theorem_1_full_credit (K : Costs) (c1 : ℝ)
    (hc : K.c < c1) (hp : c1 < K.p) :
    (c1 - K.p - K.g) +
      (K.p + K.g2 - K.c) * (K.p + K.g - c1) / (K.p + K.g2 - K.c3) ≠ 0 := by sorry

end PerishableReturns.Suboptimal
