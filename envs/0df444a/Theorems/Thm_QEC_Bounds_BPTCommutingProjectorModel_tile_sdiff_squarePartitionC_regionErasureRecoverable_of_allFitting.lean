-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allFitting
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allFitting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:23:37.912198+00:00
-- url     : https://prove2.me/theorems/93b90148-01c4-4bc8-9848-727f10aa6a54
-- title:
--   BPTCommuting Projector Model: tile sdiff square Partition C region Erasure Recoverable of all Fitting
-- statement:
--   A C-cut tile inherits recovery from the fully present tile containing it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2315-L2332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2315-L2332

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tile_sdiff_squarePartitionC_regionErasureRecoverable_of_allFitting
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin tileRows tileColumns : Nat}
    (hblockWidth : 0 < blockWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hall : M.AllFittingSquaresRecoverable blockWidth) (index : Nat × Nat)
    (hindex : index ∈ L.lattice.occupiedTileIndices blockWidth) :
    M.RegionErasureRecoverable
      (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin) := by sorry
