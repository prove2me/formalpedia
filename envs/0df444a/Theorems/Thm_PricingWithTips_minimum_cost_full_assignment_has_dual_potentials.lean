-- Prove2me | Theorems.Thm_PricingWithTips_minimum_cost_full_assignment_has_dual_potentials
-- name    : PricingWithTips.minimum_cost_full_assignment_has_dual_potentials
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:35:40.212683+00:00
-- url     : https://prove2.me/theorems/a7f83006-4097-41ad-83d5-15c61ee2381e
-- title:
--   Assignment dual potentials for a minimum-cost full courier matching
-- statement:
--   Let a feasible allocation use every courier and minimize total courier cost among allocations with the same buyer–store orders. There are a constant $C$, nonnegative courier potentials $u_d$, and order potentials $v_{bs}$ such that
--
--   $$C-c_d(b,s) \leq u_d+v_{bs}$$
--
--   for every courier and order, with equality on each courier–order assignment in the allocation. The resulting tight dual certificate is the assignment-game ingredient used to support the corrected full-courier equilibrium claim.
-- source:
--   https://arxiv.org/abs/2507.10872, Section 3.1, Lemma 3.3 and Appendix B; finite assignment-game duality for the minimum-cost matching that covers all fixed orders.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

/-- The finite assignment-duality certificate for a cost-minimal courier assignment. -/
theorem minimum_cost_full_assignment_has_dual_potentials [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d)
    (hminimum : ∀ A' : Allocation B S D,
      (∀ b, (A'.assigned b).map Prod.fst = (A.assigned b).map Prod.fst) →
        welfare M A' ≤ welfare M A) :
    ∃ (C : ℝ) (u : D → ℝ) (v : B → S → ℝ),
      (∀ d, 0 ≤ u d) ∧
      (∀ d b s, C - M.cost d b s ≤ u d + v b s) ∧
      (∀ d b s, A.Trades b s d → u d + v b s = C - M.cost d b s) := by sorry

end PricingWithTips
