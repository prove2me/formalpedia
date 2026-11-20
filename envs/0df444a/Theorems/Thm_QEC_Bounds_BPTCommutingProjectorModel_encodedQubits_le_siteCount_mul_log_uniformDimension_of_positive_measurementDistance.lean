-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_encodedQubits_le_siteCount_mul_log_uniformDimension_of_positive_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_le_siteCount_mul_log_uniformDimension_of_positive_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:22.04673+00:00
-- url     : https://prove2.me/theorems/bf3529fc-eccb-4cee-a7d6-2867aa73b0e0
-- title:
--   BPTCommuting Projector Model: encoded Qubits le site Count mul log uniform Dimension of positive measurement Distance
-- statement:
--   The finite global entropy/dimension estimate used only in the small-distance
--   branch.  It is derived from the exact BPT entropy theorem with two genuinely
--   empty recoverable regions, never from the desired tradeoff conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2659-L2711
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2659-L2711

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

theorem QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_le_siteCount_mul_log_uniformDimension_of_positive_measurementDistance
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance : Nat) (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hpositive : 0 < distance) :
    (parameter.encodedQubits : Real) ≤
      (L.lattice.siteCount : Real) * Real.logb 2 (L.uniformDimensionBound : Real) := by sorry
