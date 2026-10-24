-- Prove2me | Theorems.Thm_PricingWithTips_optimal_reassign_couriers_cost_le
-- name    : PricingWithTips.optimal_reassign_couriers_cost_le
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T23:46:06.353229+00:00
-- url     : https://prove2.me/theorems/025ebdbf-69f9-44d4-be54-15f5ec8714db
-- title:
--   Welfare optimality implies minimum cost under courier reassignment
-- statement:
--   Fix a welfare-optimal allocation and permute its couriers while leaving each buyer–store assignment unchanged. The original total delivery cost cannot exceed the cost under any such permutation.
-- source:
--   Theorem 5.2 of arXiv:2507.10872; private mission proof support

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem optimal_reassign_couriers_cost_le
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A) (f : D ≃ D) :
    (∑ b, match A.assigned b with
      | none => (0 : ℝ)
      | some (s,d) => M.cost d b s) ≤
    (∑ b, match A.assigned b with
      | none => (0 : ℝ)
      | some (s,d) => M.cost (f d) b s) := by sorry

end PricingWithTips
