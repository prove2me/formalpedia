-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_squarePartitionBComponent_externalBoundary_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.squarePartitionBComponent_externalBoundary_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:13.485801+00:00
-- url     : https://prove2.me/theorems/23cee2e0-6518-4973-92d7-06e7cb04aaca
-- title:
--   BPTCommuting Projector Model: square Partition BComponent external Boundary region Erasure Recoverable of thirtyfour mul lt measurement Distance
-- statement:
--   A B component obtains its #403 external-boundary premise from the proved thin cover.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2388-L2402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2388-L2402

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

theorem QEC.Bounds.BPTCommutingProjectorModel.squarePartitionBComponent_externalBoundary_regionErasureRecoverable_of_thirtyfour_mul_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    {blockWidth margin : Nat} (hblockWidth : 0 < blockWidth)
    (hmargin : M.interactionRange ≤ margin)
    (hwidth : margin + margin ≤ blockWidth)
    (hthin : 34 * margin * blockWidth < distance) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionBComponents blockWidth margin) :
    M.RegionErasureRecoverable (M.externalBoundary block) := by sorry
