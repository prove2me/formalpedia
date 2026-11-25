-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
-- name    : SimpleGraph.Reservoir.ofPool_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:18.817542+00:00
-- url     : https://prove2.me/theorems/ac2f617a-4395-464a-b766-b31f99aa3ad0
-- title:
--   Reservoir: of Pool pool
-- statement:
--   The starting reservoir's pool is the given set.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L91-L91
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L91-L91

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

theorem SimpleGraph.Reservoir.ofPool_pool (X : Finset V) : (ofPool (G := G) X).pool = X := by sorry

attribute [defeq] SimpleGraph.Reservoir.ofPool_pool
