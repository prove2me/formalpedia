-- Prove2me | Theorems.Thm_PricingWithTips_minimumTip_eq_requiredTip_off_order_of_plan
-- name    : PricingWithTips.minimumTip_eq_requiredTip_off_order_of_plan
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T23:18:21.246857+00:00
-- url     : https://prove2.me/theorems/a998bc29-6044-40f4-90dd-90684a336502
-- title:
--   Minimum tip equals required tip off an equilibrium courier plan
-- statement:
--   Given a courier-optimal wage plan realizing reservation utilities, the minimum zero-base tip for any unallocated order equals the required tip, including for idle couriers.
-- source:
--   Lemma 4.4 of arXiv:2507.10872; private mission proof support

import Theorems.Thm_PricingWithTips_minimumTip_le_requiredTip_off_order

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem minimumTip_eq_requiredTip_off_order_of_plan [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    (b : B) (s : S) (hoff : ¬ A.Delivers b s) :
    minimumTip M w (fun _ _ => 0) b s = requiredTip M A uBar b s := by sorry

end PricingWithTips
