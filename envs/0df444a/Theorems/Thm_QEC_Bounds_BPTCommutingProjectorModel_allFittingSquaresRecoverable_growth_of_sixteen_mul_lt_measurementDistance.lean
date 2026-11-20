-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_allFittingSquaresRecoverable_growth_of_sixteen_mul_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.allFittingSquaresRecoverable_growth_of_sixteen_mul_lt_measurementDistance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:29:17.019068+00:00
-- url     : https://prove2.me/theorems/c21b027c-c75a-4c8c-81ee-8c605e960d25
-- title:
--   BPTCommuting Projector Model: all Fitting Squares Recoverable growth of sixteen mul lt measurement Distance
-- statement:
--   The BPT thin-boundary recursion lifts correctability from every fitting `R`
--   square to every fitting `(R + 2w)` square, provided the explicit finite
--   boundary bound remains below the exact #402 distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2456-L2470
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2456-L2470

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

theorem QEC.Bounds.BPTCommutingProjectorModel.allFittingSquaresRecoverable_growth_of_sixteen_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (width : Nat) (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hthin : 16 * M.interactionRange * width < distance)
    (hall : M.AllFittingSquaresRecoverable width) :
    M.AllFittingSquaresRecoverable
      (width + M.interactionRange + M.interactionRange) := by sorry
