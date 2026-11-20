-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_empty_regionErasureRecoverable_of_positive_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.empty_regionErasureRecoverable_of_positive_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:22:27.549173+00:00
-- url     : https://prove2.me/theorems/88971633-7058-4ac3-b35f-03eed71b8854
-- title:
--   BPTCommuting Projector Model: empty region Erasure Recoverable of positive measurement Distance
-- statement:
--   The empty erased region is recoverable directly from a positive exact BPT distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2646-L2652
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2646-L2652

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

theorem QEC.Bounds.BPTCommutingProjectorModel.empty_regionErasureRecoverable_of_positive_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hpositive : 0 < distance) :
    M.RegionErasureRecoverable (∅ : Finset L.Site) := by sorry
