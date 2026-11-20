-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_expandedTile_regionErasureRecoverable_of_width_sq_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.expandedTile_regionErasureRecoverable_of_width_sq_lt_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:40.130149+00:00
-- url     : https://prove2.me/theorems/b148cb1b-aa74-4fee-a524-99d580c999f3
-- title:
--   BPTCommuting Projector Model: expanded Tile region Erasure Recoverable of width sq lt measurement Distance
-- statement:
--   The explicit local expansion of a tile is recoverable below the #402 distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2505-L2514
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2505-L2514

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

theorem QEC.Bounds.BPTCommutingProjectorModel.expandedTile_regionErasureRecoverable_of_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance blockWidth margin : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (index : Nat × Nat)
    (hwidth : (blockWidth + margin + margin) * (blockWidth + margin + margin) < distance) :
    M.RegionErasureRecoverable (L.lattice.expandedTile blockWidth margin index) := by sorry
