-- Prove2me | Theorems.Thm_PricingWithTips_maximalCourierUtility_exists_of_plan
-- name    : PricingWithTips.maximalCourierUtility_exists_of_plan
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T23:46:52.473988+00:00
-- url     : https://prove2.me/theorems/9ed7d276-bb71-4bbf-8816-3f6f5d84578e
-- title:
--   A feasible nonfull courier plan has a componentwise maximal utility profile
-- statement:
--   Fix a finite allocation with at least one idle courier. If it admits any incentive-compatible courier wage plan, then it admits a plan whose realized utility for every courier weakly dominates that courier’s utility in every other feasible plan. This makes the paper’s maximal utility profile well-defined once plan feasibility is shown.
-- source:
--   Lemma 3.2 of arXiv:2507.10872; private mission proof support

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem maximalCourierUtility_exists_of_plan
    (M : Market B S D) (A : Allocation B S D)
    (hplan0 : ∃ w : B → S → ℝ, IsCourierPlanFor M A w)
    (hnotfull : ¬ ∀ d, A.CourierWorks d) :
    ∃ uBar : D → ℝ, IsMaximalCourierUtility M A uBar := by sorry

end PricingWithTips
