-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allSquareBlocks
-- name    : QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allSquareBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:56.201536+00:00
-- url     : https://prove2.me/theorems/baa7a69d-0768-4eac-936b-5020011a85e3
-- title:
--   BPTCommuting Projector Model: external Boundary tile sdiff square Partition C region Erasure Recoverable of all Square Blocks
-- statement:
--   The external boundary of a core C-cut tile is recoverable from its `R` square
--   envelope. This is the source union-lemma premise at the maximal scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2757-L2775
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2757-L2775

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allSquareBlocks
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin envelopeWidth : Nat}
    (hrange : M.interactionRange ≤ margin)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth) (index : Nat × Nat) :
    M.RegionErasureRecoverable (M.externalBoundary
      (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin)) := by sorry
