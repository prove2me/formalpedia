-- Prove2me | Theorems.Thm_PricingWithTips_optimal_has_maximalCourierUtility
-- name    : PricingWithTips.optimal_has_maximalCourierUtility
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:11:28.855402+00:00
-- url     : https://prove2.me/theorems/a6c181a1-0562-4619-9fb0-5cf16c73d5e2
-- title:
--   Optimal nonfull allocations have maximal courier utility profiles
-- statement:
--   For a welfare-optimal allocation with at least one idle courier, there is a feasible courier wage plan whose realized utility profile is componentwise maximal among all such plans.
-- source:
--   Lemma 3.2 of arXiv:2507.10872; private mission proof support

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem optimal_has_maximalCourierUtility
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d) :
    ∃ uBar : D → ℝ, IsMaximalCourierUtility M A uBar := by sorry

end PricingWithTips
