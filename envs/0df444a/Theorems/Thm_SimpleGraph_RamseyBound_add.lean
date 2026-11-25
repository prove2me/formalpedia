-- Prove2me | Theorems.Thm_SimpleGraph_RamseyBound_add
-- name    : SimpleGraph.RamseyBound.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:31:56.634802+00:00
-- url     : https://prove2.me/theorems/306df34b-a484-4157-84e8-b3a4ec84bda0
-- title:
--   Ramsey Bound: add
-- statement:
--   **The Erdős–Szekeres recursion.** `R(r + 1, s + 1) ≤ R(r, s + 1) + R(r + 1, s)`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L306-L316
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L306-L316

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)

theorem SimpleGraph.RamseyBound.add {a b r s : ℕ} (ha : RamseyBound a r (s + 1))
    (hb : RamseyBound b (r + 1) s) (hab : 0 < a + b) : RamseyBound (a + b) (r + 1) (s + 1) := by sorry
