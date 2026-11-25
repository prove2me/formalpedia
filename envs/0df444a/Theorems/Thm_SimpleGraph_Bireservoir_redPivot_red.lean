-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_redPivot_red
-- name    : SimpleGraph.Bireservoir.redPivot_red
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:29:14.946862+00:00
-- url     : https://prove2.me/theorems/18a28e82-c306-4c50-805e-f1207b34bf46
-- title:
--   Bireservoir: red Pivot red
-- statement:
--   A red pivot adds the pivot vertex to the red clique.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L163-L163
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L163-L163

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

theorem SimpleGraph.Bireservoir.redPivot_red : (S.redPivot hv).red = insert v S.red := by sorry

attribute [defeq] SimpleGraph.Bireservoir.redPivot_red
