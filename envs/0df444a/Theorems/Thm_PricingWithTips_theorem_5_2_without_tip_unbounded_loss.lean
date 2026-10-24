-- Prove2me | Theorems.Thm_PricingWithTips_theorem_5_2_without_tip_unbounded_loss
-- name    : PricingWithTips.theorem_5_2_without_tip_unbounded_loss
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T19:48:26.866477+00:00
-- url     : https://prove2.me/theorems/aada2604-e23b-4d65-9158-f90699cec1ea
-- title:
--   Theorem 5.2(b) — unbounded welfare loss without tips
-- statement:
--   For every loss threshold $K>0$, there is a structured two-buyer, one-store, two-courier market with positive optimal welfare and at least one without-tip equilibrium in which every without-tip equilibrium has welfare at most $-K$.
-- source:
--   Gonczarowski, Ma, and Parkes (2025), Pricing with Tips in Three-Sided Delivery Platforms, arXiv:2507.10872v1, PDF p. 24, Theorem 5.2, negative clause; based on Example 2.1, PDF pp. 10–11, https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

theorem theorem_5_2_without_tip_unbounded_loss :
    ArbitrarilyLowWithoutTipWelfare := by sorry

end PricingWithTips
