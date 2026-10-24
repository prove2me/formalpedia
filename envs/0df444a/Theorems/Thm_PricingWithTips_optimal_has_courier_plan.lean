-- Prove2me | Theorems.Thm_PricingWithTips_optimal_has_courier_plan
-- name    : PricingWithTips.optimal_has_courier_plan
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:07:35.293991+00:00
-- url     : https://prove2.me/theorems/7f20b090-97b9-4c6d-950d-cac91c0bff0d
-- title:
--   A welfare-optimal allocation admits a feasible courier wage plan
-- statement:
--   For any welfare-optimal feasible allocation in a finite delivery market, there exists a nonnegative wage schedule under which assigned couriers weakly prefer their assigned orders, idle couriers do not prefer an order, and undelivered orders have zero wage. The proof uses assignment-game duality on fixed courier slots.
-- source:
--   Lemma 3.2 of arXiv:2507.10872; private mission proof support

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem optimal_has_courier_plan
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A) :
    ∃ w : B → S → ℝ, IsCourierPlanFor M A w := by sorry

end PricingWithTips
