-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tile_regionErasureRecoverable_of_allSquareBlocks
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tile_regionErasureRecoverable_of_allSquareBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:23:46.985165+00:00
-- url     : https://prove2.me/theorems/5910a0ad-6cd5-4c14-b0ab-2ab80c30a6c6
-- title:
--   BPTCommuting Projector Model: tile region Erasure Recoverable of all Square Blocks
-- statement:
--   An envelope-recoverable square recovers every smaller core tile it contains.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2741-L2751
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2741-L2751

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tile_regionErasureRecoverable_of_allSquareBlocks
    (M : BPTCommutingProjectorModel L kappa) {blockWidth envelopeWidth : Nat}
    (hwidth : blockWidth ≤ envelopeWidth)
    (hall : M.AllSquareBlocksRecoverable envelopeWidth) (index : Nat × Nat) :
    M.RegionErasureRecoverable (L.lattice.tile blockWidth index) := by sorry
