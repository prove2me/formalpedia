-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_square_regionErasureRecoverable_growth_of_sixteen_mul_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.square_regionErasureRecoverable_growth_of_sixteen_mul_lt_measurementDistance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:20:37.216938+00:00
-- url     : https://prove2.me/theorems/aa9871c2-d58d-4526-82cc-a12d49ad2825
-- title:
--   BPTCommuting Projector Model: square region Erasure Recoverable growth of sixteen mul lt measurement Distance
-- statement:
--   One exact BPT #370 growth step.  Starting from the inner square of a proposed
--   larger block, the proved thin `B union C` recovery and actual boundary cover
--   make #370 recover the larger square itself.  No maximality assumption is
--   smuggled into this local step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2110-L2161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2110-L2161

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

theorem QEC.Bounds.BPTCommutingProjectorModel.square_regionErasureRecoverable_growth_of_sixteen_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (targetOrigin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hthin : 16 * M.interactionRange * width < distance)
    (hinner : M.RegionErasureRecoverable
      (L.lattice.square (targetOrigin.1 + M.interactionRange,
        targetOrigin.2 + M.interactionRange) width)) :
    M.RegionErasureRecoverable
      (L.lattice.square targetOrigin (width + M.interactionRange + M.interactionRange)) := by sorry
