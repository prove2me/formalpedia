-- Prove2me | Theorems.Thm_PricingWithTips_full_courier_assignment_equiv_orders
-- name    : PricingWithTips.full_courier_assignment_equiv_orders
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:47:51.100102+00:00
-- url     : https://prove2.me/theorems/17730b3d-022b-47aa-bf6b-5391085f4f8d
-- title:
--   Working couriers correspond bijectively to delivered orders
-- statement:
--   Let a feasible allocation assign every courier to a delivery. Each working courier has exactly one assigned buyer–store order, and every delivered order has exactly one courier. Consequently the set of couriers is in bijection with the set of delivered orders, with each courier matched to the order she actually carries.
--
--   This identifies the allocation with a perfect matching in the courier–order assignment game.
-- source:
--   https://arxiv.org/abs/2507.10872, Section 3.1, definition of courier plans and Lemma 3.3; direct consequence of feasibility and all couriers working.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem full_courier_assignment_equiv_orders
    (A : Allocation B S D) (hfull : ∀ d, A.CourierWorks d) :
    ∃ e : D ≃ {p : B × S // A.Delivers p.1 p.2},
      ∀ d, A.Trades (e d).1.1 (e d).1.2 d := by sorry

end PricingWithTips
