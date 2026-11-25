-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
-- name    : SimpleGraph.Reservoir.ofPool_spine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:13.622858+00:00
-- url     : https://prove2.me/theorems/42b01cab-5ca5-4648-8446-bab00ac2d894
-- title:
--   Reservoir: of Pool spine
-- statement:
--   The starting reservoir has an empty spine.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L88-L88
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L88-L88

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

theorem SimpleGraph.Reservoir.ofPool_spine (X : Finset V) : (ofPool (G := G) X).spine = ∅ := by sorry

attribute [defeq] SimpleGraph.Reservoir.ofPool_spine
