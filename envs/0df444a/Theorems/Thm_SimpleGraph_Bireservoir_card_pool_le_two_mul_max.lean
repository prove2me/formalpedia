-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_card_pool_le_two_mul_max
-- name    : SimpleGraph.Bireservoir.card_pool_le_two_mul_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:31:56.638477+00:00
-- url     : https://prove2.me/theorems/e5b8370b-361f-4860-be0e-b9f6f84d6554
-- title:
--   Bireservoir: card pool le two mul max
-- statement:
--   One of the two moves keeps at least half of the remaining pool.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L203-L206
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L203-L206

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
open SimpleGraph.Bireservoir
variable {G}
variable (S : G.Bireservoir)
variable [DecidableEq V] [DecidableRel G.Adj] {v : V} (hv : v ∈ S.pool)

theorem SimpleGraph.Bireservoir.card_pool_le_two_mul_max :
    #S.pool ≤ 2 * max #(S.redPivot hv).pool #(S.bluePivot hv).pool + 1 := by sorry
