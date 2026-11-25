-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_redPivot_pool
-- name    : SimpleGraph.Bireservoir.redPivot_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:29:17.152799+00:00
-- url     : https://prove2.me/theorems/750abf5d-0ffc-4d82-8d2d-c74b9e8ad2e5
-- title:
--   Bireservoir: red Pivot pool
-- statement:
--   A red pivot keeps the pivot's red neighbours in the pool.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L169-L169
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L169-L169

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

theorem SimpleGraph.Bireservoir.redPivot_pool : (S.redPivot hv).pool = {w ∈ S.pool | G.Adj v w} := by sorry

attribute [defeq] SimpleGraph.Bireservoir.redPivot_pool
