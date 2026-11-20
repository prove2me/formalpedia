-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalBoundary_regionErasureRecoverable_of_expandedTile_width_sq_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_regionErasureRecoverable_of_expandedTile_width_sq_lt_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:29:20.742239+00:00
-- url     : https://prove2.me/theorems/d8283ee0-9f3a-4ffc-a867-c8ab9a089194
-- title:
--   BPTCommuting Projector Model: external Boundary region Erasure Recoverable of expanded Tile width sq lt measurement Distance
-- statement:
--   An external boundary has a typed recovery when its proved local expanded-tile
--   cover is below the #402 distance.  The explicit expanded-square condition is
--   kept in the statement; this is not the later thin-boundary source estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2521-L2535
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2521-L2535

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

theorem QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_regionErasureRecoverable_of_expandedTile_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance blockWidth margin : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (index : Nat × Nat) (block : Finset L.Site)
    (hblock : block ⊆ L.lattice.tile blockWidth index)
    (hrange : M.interactionRange ≤ margin)
    (hwidth : (blockWidth + margin + margin) * (blockWidth + margin + margin) < distance) :
    M.RegionErasureRecoverable (M.externalBoundary block) := by sorry
