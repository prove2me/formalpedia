-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_allSquareBlocksRecoverable_growth_of_sixteen_mul_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.allSquareBlocksRecoverable_growth_of_sixteen_mul_lt_measurementDistance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:26:48.155369+00:00
-- url     : https://prove2.me/theorems/383067f0-7b94-435b-8639-05fb31d0cedd
-- title:
--   BPTCommuting Projector Model: all Square Blocks Recoverable growth of sixteen mul lt measurement Distance
-- statement:
--   The same #370 step lifts every open-boundary square block, without a fit side condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2473-L2485
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2473-L2485

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

theorem QEC.Bounds.BPTCommutingProjectorModel.allSquareBlocksRecoverable_growth_of_sixteen_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (width : Nat) (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hthin : 16 * M.interactionRange * width < distance)
    (hall : M.AllSquareBlocksRecoverable width) :
    M.AllSquareBlocksRecoverable
      (width + M.interactionRange + M.interactionRange) := by sorry
