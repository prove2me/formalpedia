-- Prove2me | Theorems.Thm_SimpleGraph_HomogeneousBlocks_isNClique_map_rep
-- name    : SimpleGraph.HomogeneousBlocks.isNClique_map_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:18.402585+00:00
-- url     : https://prove2.me/theorems/b1374436-4715-4cee-ad8e-c5d24d4f5695
-- title:
--   Homogeneous Blocks: is NClique map rep
-- statement:
--   Cliques of the quotient lift to cliques of `G`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L116-L122
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L116-L122

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

theorem SimpleGraph.HomogeneousBlocks.isNClique_map_rep {m : ℕ} {I : Finset ι} (hI : F.quotient.IsNClique m I) :
    G.IsNClique m (I.map F.repEmbedding) := by sorry
