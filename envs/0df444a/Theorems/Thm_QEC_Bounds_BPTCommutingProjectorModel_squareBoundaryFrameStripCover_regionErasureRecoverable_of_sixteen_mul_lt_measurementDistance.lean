-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_squareBoundaryFrameStripCover_regionErasureRecoverable_of_sixteen_mul_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.squareBoundaryFrameStripCover_regionErasureRecoverable_of_sixteen_mul_lt_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:03.198633+00:00
-- url     : https://prove2.me/theorems/7d0b5658-db8a-4f49-8836-f91ff4eac41e
-- title:
--   BPTCommuting Projector Model: square Boundary Frame Strip Cover region Erasure Recoverable of sixteen mul lt measurement Distance
-- statement:
--   The source thin-boundary estimate gives a concrete #402 CPTP recovery for the
--   full finite `B union C` strip cover when its explicit `16*w*R` bound is below
--   the BPT measurement distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2064-L2074
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2064-L2074

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

theorem QEC.Bounds.BPTCommutingProjectorModel.squareBoundaryFrameStripCover_regionErasureRecoverable_of_sixteen_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (origin : Nat × Nat) (width : Nat)
    (hwidth : M.interactionRange + M.interactionRange ≤ width)
    (hthin : 16 * M.interactionRange * width < distance) :
    M.RegionErasureRecoverable
      (L.lattice.squareBoundaryFrameStripCover origin width M.interactionRange) := by sorry
