-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_squarePartitionB_regionErasureRecoverable_of_allSquareBlocks_or_empty
-- name    : QEC.Bounds.BPTCommutingProjectorModel.squarePartitionB_regionErasureRecoverable_of_allSquareBlocks_or_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:28:09.122126+00:00
-- url     : https://prove2.me/theorems/a6b0fb96-1c76-4b0a-b9bf-e28fc97a115b
-- title:
--   BPTCommuting Projector Model: square Partition B region Erasure Recoverable of all Square Blocks or empty
-- statement:
--   The matching empty-or-assembled construction removes the nonempty-B input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2873-L2890
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2873-L2890

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

theorem QEC.Bounds.BPTCommutingProjectorModel.squarePartitionB_regionErasureRecoverable_of_allSquareBlocks_or_empty
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin envelopeWidth : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth)
    (hempty : M.RegionErasureRecoverable (∅ : Finset L.Site)) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin) := by sorry
