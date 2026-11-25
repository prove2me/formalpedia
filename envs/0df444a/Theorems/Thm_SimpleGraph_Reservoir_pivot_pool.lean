-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
-- name    : SimpleGraph.Reservoir.pivot_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:21.084654+00:00
-- url     : https://prove2.me/theorems/18898268-0c53-49d7-8df8-dd191075f932
-- title:
--   Reservoir: pivot pool
-- statement:
--   A pivot keeps the pivot's neighbours in the pool.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L151-L151
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L151-L151

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Reservoir
variable {G}
variable (R : G.Reservoir)
variable [DecidableRel G.Adj] [DecidableEq V]
variable {v : V} (hv : v ∈ R.pool)

theorem SimpleGraph.Reservoir.pivot_pool : (R.pivot v hv).pool = {w ∈ R.pool | G.Adj v w} := by sorry

attribute [defeq] SimpleGraph.Reservoir.pivot_pool
