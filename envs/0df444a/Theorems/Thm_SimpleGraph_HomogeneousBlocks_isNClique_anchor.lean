-- Prove2me | Theorems.Thm_SimpleGraph_HomogeneousBlocks_isNClique_anchor
-- name    : SimpleGraph.HomogeneousBlocks.isNClique_anchor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:18.008093+00:00
-- url     : https://prove2.me/theorems/ca28ac66-ab2d-49b2-b8d6-33c4566085bf
-- title:
--   Homogeneous Blocks: is NClique anchor
-- statement:
--   **Anchored gluing.** If `I` is an `m`-clique of the quotient containing `i₀`, and `t` is an
--   `n`-clique of `G` inside the block `i₀`, then `t` together with the representatives of the other
--   blocks of `I` is an `(n + m - 1)`-clique of `G`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L137-L156
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/HomogeneousBlocks.lean#L137-L156

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

theorem SimpleGraph.HomogeneousBlocks.isNClique_anchor [DecidableEq V] [DecidableEq ι] {m n : ℕ} {I : Finset ι}
    (hI : F.quotient.IsNClique m I) {i₀ : ι} (hi₀ : i₀ ∈ I) {t : Finset V}
    (ht : G.IsNClique n t) (hts : t ⊆ F.block i₀) :
    G.IsNClique (n + m - 1) (t ∪ (I.erase i₀).map F.repEmbedding) := by sorry
