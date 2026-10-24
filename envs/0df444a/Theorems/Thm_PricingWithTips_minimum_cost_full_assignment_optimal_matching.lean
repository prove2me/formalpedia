-- Prove2me | Theorems.Thm_PricingWithTips_minimum_cost_full_assignment_optimal_matching
-- name    : PricingWithTips.minimum_cost_full_assignment_optimal_matching
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:03:04.407844+00:00
-- url     : https://prove2.me/theorems/6774a9fa-7664-4174-8684-343a9c75aacd
-- title:
--   Minimum courier cost gives a maximum-gain assignment matching
-- statement:
--   Fix the buyer–store orders of a feasible allocation that uses every courier. Identify the couriers bijectively with their assigned orders. If the allocation has minimum total courier cost among all allocations with those same orders, then for any constant $C$ strictly larger than every courier–order cost, its courier–order matching maximizes the total gain $C-c_d(b,s)$ among all partial matchings.
--
--   This is the finite matching step needed to apply assignment-game complementary slackness to supporting courier wages.
-- source:
--   https://arxiv.org/abs/2507.10872, Section 3.1, Lemma 3.3; equivalence between minimum-cost courier assignment and maximum-gain matching after a positive constant shift.

import Definitions.Def_PricingWithTips_Model
import Definitions.Def_AssignmentGame_CoreCorners_Game

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

/-- Reinterpret minimum courier cost as maximum shifted gain in the assignment game. -/
theorem minimum_cost_full_assignment_optimal_matching
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d)
    (hminimum : ∀ A' : Allocation B S D,
      (∀ b, (A'.assigned b).map Prod.fst = (A.assigned b).map Prod.fst) →
        welfare M A' ≤ welfare M A)
    (e : D ≃ {p : B × S // A.Delivers p.1 p.2})
    (he : ∀ d, A.Trades (e d).1.1 (e d).1.2 d)
    (C : ℝ) (hC : ∀ d b s, M.cost d b s < C) :
    (∑ d, (C - M.cost d (e d).1.1 (e d).1.2)) =
      (by
        classical
        exact AssignmentGame.CoreCorners.worth
          (fun d (o : {p : B × S // A.Delivers p.1 p.2}) =>
            C - M.cost d o.1.1 o.1.2) Finset.univ Finset.univ) := by sorry

end PricingWithTips
