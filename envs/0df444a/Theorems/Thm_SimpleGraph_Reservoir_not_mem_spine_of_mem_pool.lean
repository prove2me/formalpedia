-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_not_mem_spine_of_mem_pool
-- name    : SimpleGraph.Reservoir.not_mem_spine_of_mem_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:18.858969+00:00
-- url     : https://prove2.me/theorems/ef0aa673-b712-502f-86a5-0c0179ba165b
-- title:
--   Reservoir: not mem spine of mem pool
-- statement:
--   Pool vertices are not on the spine.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L96-L97
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L96-L97

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

theorem SimpleGraph.Reservoir.not_mem_spine_of_mem_pool {v : V} (hv : v ∈ R.pool) : v ∉ R.spine := by sorry
