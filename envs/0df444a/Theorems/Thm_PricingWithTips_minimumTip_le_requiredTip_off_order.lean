-- Prove2me | Theorems.Thm_PricingWithTips_minimumTip_le_requiredTip_off_order
-- name    : PricingWithTips.minimumTip_le_requiredTip_off_order
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:36:23.42134+00:00
-- url     : https://prove2.me/theorems/f4d6417a-1437-4202-bccb-06efe5dd7a6f
-- title:
--   An upper bound on the minimum tip for an unserved order
-- statement:
--   Fix an unserved buyer–store order whose wage is zero. Suppose every courier’s current utility from every order is at most a nonnegative bound $u_d$. Then the minimum nonnegative tip that induces some courier to serve the order is no larger than the infimum over couriers of delivery cost plus $u_d$. Offering exactly cost plus $u_d$ makes courier $d$ willing to deliver, because her new utility is $u_d$ and all other orders yield no more. This is the upper-bound half of the paper’s minimum-tip formula for unserved orders.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, Section 4 Eq. (1), p. 18, and proof of Lemma 4.4 in Appendix C, pp. 33–34.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem minimumTip_le_requiredTip_off_order [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (b : B) (s : S)
    (hoff : ¬ A.Delivers b s)
    (hwzero : w b s = 0)
    (hu_nonneg : ∀ d, 0 ≤ uBar d)
    (hupper : ∀ d b' s', w b' s' - M.cost d b' s' ≤ uBar d) :
    minimumTip M w (fun _ _ => 0) b s ≤ requiredTip M A uBar b s := by sorry

end PricingWithTips
