-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_locallyMaximalCorrectableSquareScale_of_four_mul_width_sq_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_locallyMaximalCorrectableSquareScale_of_four_mul_width_sq_lt_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:25:49.443257+00:00
-- url     : https://prove2.me/theorems/b4541f88-374c-40c4-868a-312a921248e3
-- title:
--   BPTCommuting Projector Model: exists locally Maximal Correctable Square Scale of four mul width sq lt measurement Distance
-- statement:
--   The exact finite `4w` source seed constructs a locally maximal square scale
--   whenever the encoded-qubit parameter is nonzero.  This is the finite version
--   of the source's choice of its largest recoverable square, before any
--   checkerboard geometry is applied.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2302-L2312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2302-L2312

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

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_locallyMaximalCorrectableSquareScale_of_four_mul_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (distance : Nat) (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hseed : (4 * M.interactionRange) * (4 * M.interactionRange) < distance)
    (hpositive : 0 < parameter.encodedQubits) :
    ∃ width, 4 * M.interactionRange ≤ width ∧
      M.LocallyMaximalCorrectableSquareScale width := by sorry
