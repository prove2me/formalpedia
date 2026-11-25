-- Prove2me | Theorems.Thm_SimpleGraph_HomogeneousBlocks_quotient_adj
-- name    : SimpleGraph.HomogeneousBlocks.quotient_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:02.405894+00:00
-- url     : https://prove2.me/theorems/4b77a3b4-b182-53fa-85d7-e15dd7569bd4
-- title:
--   Homogeneous Blocks: quotient adj
-- statement:
--   Adjacency in the quotient: distinct blocks joined in `G`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L65-L68
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L65-L68

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

theorem SimpleGraph.HomogeneousBlocks.quotient_adj {i j : ι} :
    F.quotient.Adj i j ↔ i ≠ j ∧ ∀ x ∈ F.block i, ∀ y ∈ F.block j, G.Adj x y := by sorry
