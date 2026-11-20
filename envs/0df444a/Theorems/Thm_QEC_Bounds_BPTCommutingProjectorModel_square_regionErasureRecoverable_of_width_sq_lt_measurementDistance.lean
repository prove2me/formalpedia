-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_square_regionErasureRecoverable_of_width_sq_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.square_regionErasureRecoverable_of_width_sq_lt_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:37.341721+00:00
-- url     : https://prove2.me/theorems/46112274-d158-4d37-b855-53419012d99e
-- title:
--   BPTCommuting Projector Model: square region Erasure Recoverable of width sq lt measurement Distance
-- statement:
--   Every source square whose finite area is strictly below the BPT measurement
--   distance is concretely erasure-recoverable.  This is the distance seed used
--   by the later square-growth and separated-union arguments.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2051-L2057
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2051-L2057

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

theorem QEC.Bounds.BPTCommutingProjectorModel.square_regionErasureRecoverable_of_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (origin : Nat × Nat) (width : Nat) (hwidth : width * width < distance) :
    M.RegionErasureRecoverable (L.lattice.square origin width) := by sorry
