-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_pool
-- name    : SimpleGraph.Bireservoir.bluePivot_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:29:19.072934+00:00
-- url     : https://prove2.me/theorems/e59b11e6-e6c9-4337-9b9a-efda23891787
-- title:
--   Bireservoir: blue Pivot pool
-- statement:
--   A blue pivot keeps the pivot's blue neighbours in the pool.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L178-L178
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L178-L178

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

theorem SimpleGraph.Bireservoir.bluePivot_pool : (S.bluePivot hv).pool = {w ∈ S.pool | Gᶜ.Adj v w} := by sorry

attribute [defeq] SimpleGraph.Bireservoir.bluePivot_pool
