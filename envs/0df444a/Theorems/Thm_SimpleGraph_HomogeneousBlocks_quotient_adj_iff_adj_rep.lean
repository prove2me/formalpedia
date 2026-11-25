-- Prove2me | Theorems.Thm_SimpleGraph_HomogeneousBlocks_quotient_adj_iff_adj_rep
-- name    : SimpleGraph.HomogeneousBlocks.quotient_adj_iff_adj_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:49.873619+00:00
-- url     : https://prove2.me/theorems/27456461-a730-4886-8e00-46dc88a0ef0e
-- title:
--   Homogeneous Blocks: quotient adj iff adj rep
-- statement:
--   The quotient is the graph induced on the representatives.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L108-L113
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L108-L113

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

theorem SimpleGraph.HomogeneousBlocks.quotient_adj_iff_adj_rep {i j : ι} : F.quotient.Adj i j ↔ G.Adj (F.rep i) (F.rep j) := by sorry
