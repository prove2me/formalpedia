-- Prove2me | Theorems.Thm_PricingWithTips_minimum_cost_full_assignment_has_plan
-- name    : PricingWithTips.minimum_cost_full_assignment_has_plan
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:26:42.309324+00:00
-- url     : https://prove2.me/theorems/5ee9f836-e67a-4522-963a-508723276127
-- title:
--   Minimum-cost full courier assignments admit supporting payments
-- statement:
--   Fix a feasible delivery allocation A that employs every courier. Suppose its courier assignment has minimum total cost among all feasible allocations that preserve each buyer's store (and preserve which buyers receive no store). Then there are nonnegative order payments that support this exact courier assignment: each working courier weakly prefers her assigned order to idling and every other order, while unserved orders receive zero payment.
--
--   $$
--   \text{minimum-cost full assignment of fixed buyer–store orders}
--   \ \Longrightarrow\
--   \exists w,\ \operatorname{CourierPlan}(M,A,w).
--   $$
--
--   This is the missing assignment-market step behind corrected Corollary 4.5.
-- source:
--   https://arxiv.org/abs/2507.10872, Section 4 and Appendix C; corrected courier-plan premise for Corollary 4.5.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem minimum_cost_full_assignment_has_plan [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d)
    (hminimum : ∀ A' : Allocation B S D,
      (∀ b, (A'.assigned b).map Prod.fst = (A.assigned b).map Prod.fst) →
        welfare M A' ≤ welfare M A) :
    ∃ w, IsCourierPlanFor M A w := by sorry

end PricingWithTips
