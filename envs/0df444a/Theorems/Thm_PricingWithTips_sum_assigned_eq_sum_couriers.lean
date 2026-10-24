-- Prove2me | Theorems.Thm_PricingWithTips_sum_assigned_eq_sum_couriers
-- name    : PricingWithTips.sum_assigned_eq_sum_couriers
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:15:42.201023+00:00
-- url     : https://prove2.me/theorems/c78cd2b3-b4ca-4c62-8f47-a9b749bd6ba4
-- title:
--   Reindex delivered-order sums from buyers to couriers
-- statement:
--   For a feasible allocation in which couriers are bijectively identified with delivered buyer–store orders, any sum of order payoffs may be indexed either by buyers with an assigned order or by couriers. Unassigned buyers contribute zero.
--
--   This reindexing identity converts the market’s buyer-indexed welfare formula into the courier-indexed cost expression used by the assignment game.
-- source:
--   https://arxiv.org/abs/2507.10872, Section 2 allocation and welfare definitions, and Section 3.1 courier–order matching construction.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem sum_assigned_eq_sum_couriers
    (A : Allocation B S D)
    (e : D ≃ {p : B × S // A.Delivers p.1 p.2})
    (he : ∀ d, A.Trades (e d).1.1 (e d).1.2 d)
    (F : D → B → S → ℝ) :
    (∑ b, match A.assigned b with
      | none => 0
      | some (s, d) => F d b s) =
    ∑ d, F d (e d).1.1 (e d).1.2 := by sorry

end PricingWithTips
