-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_squarePartitionBComponent_regionErasureRecoverable_of_allSquareBlocks
-- name    : QEC.Bounds.BPTCommutingProjectorModel.squarePartitionBComponent_regionErasureRecoverable_of_allSquareBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:19.646053+00:00
-- url     : https://prove2.me/theorems/57593feb-4b36-4b90-b6c9-d2344b6d8b01
-- title:
--   BPTCommuting Projector Model: square Partition BComponent region Erasure Recoverable of all Square Blocks
-- statement:
--   Every odd checkerboard core is recoverable from a same-origin square envelope.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2793-L2805
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2793-L2805

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

theorem QEC.Bounds.BPTCommutingProjectorModel.squarePartitionBComponent_regionErasureRecoverable_of_allSquareBlocks
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin envelopeWidth : Nat}
    (hblockWidth : 0 < blockWidth) (hwidth : blockWidth ≤ envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionBComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by sorry
