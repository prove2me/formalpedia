-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_allSquareBlocksRecoverable_of_width_sq_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.allSquareBlocksRecoverable_of_width_sq_lt_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:27:09.652557+00:00
-- url     : https://prove2.me/theorems/09b8862b-f918-495d-af44-3a86275d2d4e
-- title:
--   BPTCommuting Projector Model: all Square Blocks Recoverable of width sq lt measurement Distance
-- statement:
--   A source square-area seed makes every open-boundary square at that scale recoverable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2287-L2294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2287-L2294

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

theorem QEC.Bounds.BPTCommutingProjectorModel.allSquareBlocksRecoverable_of_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance width : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hwidth : width * width < distance) :
    M.AllSquareBlocksRecoverable width := by sorry
