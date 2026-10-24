-- Prove2me | Theorems.Thm_PricingWithTips_minimumTip_le_requiredTip_off_order_with_tips
-- name    : PricingWithTips.minimumTip_le_requiredTip_off_order_with_tips
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:47:53.834462+00:00
-- url     : https://prove2.me/theorems/db3ad020-bc1f-4628-9f72-9969313cfb3b
-- title:
--   Minimum tip bound with arbitrary existing tips
-- statement:
--   For an unserved order with zero wage, suppose all existing tips are nonnegative and every courier’s utility on every order is at most a nonnegative bound $u_d$. Even with the original tip schedule in place, offering courier $d$ a counterfactual tip equal to delivery cost plus $u_d$ makes that courier willing to serve the order. Hence the minimum admissible tip is at most the infimum of these cost-plus-utility bounds over couriers. This removes the zero-tip normalization from the only-if proof of Lemma 4.4.
-- source:
--   Pricing with Tips, https://arxiv.org/abs/2507.10872, Section 4 Eq. (1), p. 18, and Lemma 4.4 proof in Appendix C, pp. 33–34.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem minimumTip_le_requiredTip_off_order_with_tips [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (w t : B → S → ℝ) (uBar : D → ℝ)
    (b : B) (s : S)
    (hoff : ¬ A.Delivers b s)
    (hwzero : w b s = 0)
    (ht_nonneg : ∀ b' s', 0 ≤ t b' s')
    (hu_nonneg : ∀ d, 0 ≤ uBar d)
    (hupper : ∀ d b' s', w b' s' + t b' s' - M.cost d b' s' ≤ uBar d) :
    minimumTip M w t b s ≤ requiredTip M A uBar b s := by sorry

end PricingWithTips
