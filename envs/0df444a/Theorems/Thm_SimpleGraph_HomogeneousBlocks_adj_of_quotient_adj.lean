-- Prove2me | Theorems.Thm_SimpleGraph_HomogeneousBlocks_adj_of_quotient_adj
-- name    : SimpleGraph.HomogeneousBlocks.adj_of_quotient_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:04.624173+00:00
-- url     : https://prove2.me/theorems/6d43f214-c11e-5949-b223-b2429af24ca2
-- title:
--   Homogeneous Blocks: adj of quotient adj
-- statement:
--   Vertices of quotient-adjacent blocks are adjacent in `G`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L71-L73
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L71-L73

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks
set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open SimpleGraph
variable {V ι : Type*}
open SimpleGraph.HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)

theorem SimpleGraph.HomogeneousBlocks.adj_of_quotient_adj {i j : ι} (h : F.quotient.Adj i j) {x y : V} (hx : x ∈ F.block i)
    (hy : y ∈ F.block j) : G.Adj x y := by sorry
