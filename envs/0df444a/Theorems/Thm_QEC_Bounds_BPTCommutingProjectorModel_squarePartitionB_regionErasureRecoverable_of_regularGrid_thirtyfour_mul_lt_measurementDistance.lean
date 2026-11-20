-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_squarePartitionB_regionErasureRecoverable_of_regularGrid_thirtyfour_mul_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.squarePartitionB_regionErasureRecoverable_of_regularGrid_thirtyfour_mul_lt_measurementDistance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:28:35.889875+00:00
-- url     : https://prove2.me/theorems/a7ac1f47-b79b-4399-810a-b89bca8a851e
-- title:
--   BPTCommuting Projector Model: square Partition B region Erasure Recoverable of regular Grid thirtyfour mul lt measurement Distance
-- statement:
--   The matching finite B checkerboard recovery assembled through the #403 induction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2430-L2449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2430-L2449

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

theorem QEC.Bounds.BPTCommutingProjectorModel.squarePartitionB_regionErasureRecoverable_of_regularGrid_thirtyfour_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    {blockWidth margin tileRows tileColumns : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth)
    (hrows : L.lattice.rows = tileRows * blockWidth)
    (hcolumns : L.lattice.columns = tileColumns * blockWidth)
    (hthin : 34 * margin * blockWidth < distance)
    (hall : M.AllFittingSquaresRecoverable blockWidth)
    (hnonempty : (L.lattice.squarePartitionBComponents blockWidth margin).Nonempty) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin) := by sorry
