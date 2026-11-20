-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_squarePartitionBComponent_regionErasureRecoverable_of_allFitting
-- name    : QEC.Bounds.BPTCommutingProjectorModel.squarePartitionBComponent_regionErasureRecoverable_of_allFitting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:25:49.397099+00:00
-- url     : https://prove2.me/theorems/ff771d2e-5c13-4693-8f37-d3a248f13784
-- title:
--   BPTCommuting Projector Model: square Partition BComponent region Erasure Recoverable of all Fitting
-- statement:
--   An odd indexed B component inherits the recoverability of its source tile.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2353-L2368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2353-L2368

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

theorem QEC.Bounds.BPTCommutingProjectorModel.squarePartitionBComponent_regionErasureRecoverable_of_allFitting
    (M : BPTCommutingProjectorModel L kappa) {blockWidth margin tileRows tileColumns : Nat}
    (hblockWidth : 0 < blockWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hall : M.AllFittingSquaresRecoverable blockWidth) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionBComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by sorry
