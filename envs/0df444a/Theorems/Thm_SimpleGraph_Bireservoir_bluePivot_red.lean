-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_red
-- name    : SimpleGraph.Bireservoir.bluePivot_red
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:28:52.745008+00:00
-- url     : https://prove2.me/theorems/9b0a3bc8-ccb3-4e69-b2f7-e7c62faba5c2
-- title:
--   Bireservoir: blue Pivot red
-- statement:
--   A blue pivot keeps the red clique.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L172-L172
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L172-L172

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

theorem SimpleGraph.Bireservoir.bluePivot_red : (S.bluePivot hv).red = S.red := by sorry

attribute [defeq] SimpleGraph.Bireservoir.bluePivot_red
