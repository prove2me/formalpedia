-- Prove2me | Theorems.Thm_SimpleGraph_HomogeneousBlocks_repEmbedding_apply
-- name    : SimpleGraph.HomogeneousBlocks.repEmbedding_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:38.893804+00:00
-- url     : https://prove2.me/theorems/927da344-b4a5-5934-994f-0359ef8f12b1
-- title:
--   Homogeneous Blocks: rep Embedding apply
-- statement:
--   The representative embedding sends a block to its representative.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L105-L105
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L105-L105

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

theorem SimpleGraph.HomogeneousBlocks.repEmbedding_apply (i : ι) : F.repEmbedding i = F.rep i := by sorry

attribute [defeq] SimpleGraph.HomogeneousBlocks.repEmbedding_apply
