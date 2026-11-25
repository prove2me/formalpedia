-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_card_redPivot_pool_add_card_bluePivot_pool
-- name    : SimpleGraph.Bireservoir.card_redPivot_pool_add_card_bluePivot_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:29:54.262295+00:00
-- url     : https://prove2.me/theorems/cb8f03d1-ef50-4214-bf44-3d0aa7529847
-- title:
--   Bireservoir: card red Pivot pool add card blue Pivot pool
-- statement:
--   **The two moves partition the pool.** Every pool vertex other than the pivot is kept by
--   exactly one of the two moves.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L190-L200
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L190-L200

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

theorem SimpleGraph.Bireservoir.card_redPivot_pool_add_card_bluePivot_pool :
    #(S.redPivot hv).pool + #(S.bluePivot hv).pool + 1 = #S.pool := by sorry
