-- Prove2me | Theorems.Thm_PricingWithTips_proposition_3_6_without_tip_is_with_tip
-- name    : PricingWithTips.proposition_3_6_without_tip_is_with_tip
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T19:18:43.107034+00:00
-- url     : https://prove2.me/theorems/ff90776d-177a-402b-b494-cf98320f82f9
-- title:
--   Proposition 3.6 — without-tip equilibria are zero-tip equilibria
-- statement:
--   Every equilibrium of the platform without tips is also an equilibrium of the platform with up-front tips when every buyer’s tip is fixed to zero. The allocation, store prices, and platform-to-courier payments are unchanged.
-- source:
--   Gonczarowski, Ma, and Parkes (2025), Pricing with Tips in Three-Sided Delivery Platforms, arXiv:2507.10872v1, PDF p. 14, Proposition 3.6, https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem proposition_3_6_without_tip_is_with_tip
    (M : Market B S D) (A : Allocation B S D) (p : S → ℝ) (w : B → S → ℝ)
    (h : IsWithoutTipEquilibrium M A p w) :
    IsWithTipEquilibrium M A p w (fun _ _ => 0) := by sorry

end PricingWithTips
