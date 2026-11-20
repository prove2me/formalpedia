-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:20:21.95581+00:00
-- url     : https://prove2.me/theorems/89a11680-a7e5-4be4-bb90-aa0407ad7b6d
-- title:
--   BPTCommuting Projector Model: external Boundary tile sdiff square Partition C region Erasure Recoverable of thirtyfour mul lt measurement Distance
-- statement:
--   Each C-cut source tile has a concrete external-boundary recovery when the
--   proved `34*w*R` cover is below the exact #402 distance.  This supplies the
--   otherwise independent #403 premise without reverting to an `R^2` adapter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2081-L2102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2081-L2102

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

theorem QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_tile_sdiff_squarePartitionC_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth)
    (hthin : 34 * margin * blockWidth < distance) (index : Nat × Nat) :
    M.RegionErasureRecoverable (M.externalBoundary
      (L.lattice.tile blockWidth index \ L.lattice.squarePartitionC blockWidth margin)) := by sorry
