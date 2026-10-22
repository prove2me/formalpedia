-- Prove2me | Theorems.Thm_RobustBooking_BidPrice_eq5_order_quantity_le
-- name    : RobustBooking.BidPrice.eq5_order_quantity_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T01:07:12.3952+00:00
-- url     : https://prove2.me/theorems/ca67a57d-35f6-49b9-86ef-b8e04d8ee62f
-- title:
--   Eq. (5) — the order quantity control satisfies P(Q(f)) ≤ f on [fmin, fmax]
-- statement:
--   Let $Q : \mathbb{R} \to \mathbb{R}$ be a protection-level control function and let $P(q) = \min\{f \in [f_{\min}, f_{\max}] : Q(f) \ge q\}$ be its order quantity control function. Then
--   $$P(Q(f)) \le f \qquad \text{for all } f_{\min} \le f \le f_{\max}.$$
--
--   This is the relation between the two controls used in Case II of the proof of Theorem 7 for the protection-level policy: an order accepted at fare $O_i$ is placed in the interval $[Q(O_i) - x_i, Q(O_i)]$, on which $O_i$ dominates $P$.
--
--   **Formalization Note.** $P$ is the real `sInf` of the set above (bounded below by $f_{\min}$). The paper states (5) for its nondecreasing $Q$; the statement here is for an arbitrary $Q$, which contains that case.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 956, §2, Eq. (5)

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy
import Definitions.Def_RobustBooking_BidPrice_Controls

namespace RobustBooking.BidPrice

/-- Eq. (5) (Ball–Queyranne 2009, §2, p. 956). Let `Q` be a protection-level control function
and `P(q) = min {f ∈ [f_min, f_max] : Q(f) ≥ q}` its order
quantity control function. Then `P(Q(f)) ≤ f` for all `f_min ≤ f ≤ f_max`. -/
theorem eq5_order_quantity_le (fmin fmax : ℝ) (Q : ℝ → ℝ) (f : ℝ) (hf : f ∈ Set.Icc fmin fmax) :
    orderQuantityControl fmin fmax Q (Q f) ≤ f := by sorry

end RobustBooking.BidPrice
