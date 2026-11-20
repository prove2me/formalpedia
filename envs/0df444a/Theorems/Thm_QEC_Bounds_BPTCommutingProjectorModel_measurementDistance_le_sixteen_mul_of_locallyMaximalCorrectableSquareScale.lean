-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_measurementDistance_le_sixteen_mul_of_locallyMaximalCorrectableSquareScale
-- name    : QEC.Bounds.BPTCommutingProjectorModel.measurementDistance_le_sixteen_mul_of_locallyMaximalCorrectableSquareScale
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:21:38.519411+00:00
-- url     : https://prove2.me/theorems/2376a243-2c51-46b4-8278-854d05e41311
-- title:
--   BPTCommuting Projector Model: measurement Distance le sixteen mul of locally Maximal Correctable Square Scale
-- statement:
--   At a locally maximal source square scale, the exact finite BPT distance is at
--   most the proved thin-boundary size `16*w*R`.  This is the source's maximality
--   contradiction in contrapositive form, with no asymptotic replacement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2492-L2502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2492-L2502

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

theorem QEC.Bounds.BPTCommutingProjectorModel.measurementDistance_le_sixteen_mul_of_locallyMaximalCorrectableSquareScale
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (width : Nat) (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hmax : M.LocallyMaximalCorrectableSquareScale width) :
    distance ≤ 16 * M.interactionRange * width := by sorry
