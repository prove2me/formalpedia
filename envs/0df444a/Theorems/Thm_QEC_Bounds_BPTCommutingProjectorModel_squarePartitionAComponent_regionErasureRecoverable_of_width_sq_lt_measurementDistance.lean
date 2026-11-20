-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_squarePartitionAComponent_regionErasureRecoverable_of_width_sq_lt_measurementDistance
-- name    : QEC.Bounds.BPTCommutingProjectorModel.squarePartitionAComponent_regionErasureRecoverable_of_width_sq_lt_measurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:28:46.679059+00:00
-- url     : https://prove2.me/theorems/54a85d87-bc29-42f2-80d3-e6276cc2a023
-- title:
--   BPTCommuting Projector Model: square Partition AComponent region Erasure Recoverable of width sq lt measurement Distance
-- statement:
--   Every concrete `A` component is correctable when its source square area is
--   strictly below the #402 BPT measurement distance.  This proves the component
--   seed directly from its finite cardinality, without changing the distance
--   convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2543-L2550
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2543-L2550

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

theorem QEC.Bounds.BPTCommutingProjectorModel.squarePartitionAComponent_regionErasureRecoverable_of_width_sq_lt_measurementDistance
    (M : BPTCommutingProjectorModel L kappa) (distance blockWidth margin : Nat)
    (hDistance : QuditSubsystem.BPTMeasurementDistance M.codeSpace distance)
    (hwidth : blockWidth * blockWidth < distance) (block : Finset L.Site)
    (hblock : block ∈ L.lattice.squarePartitionAComponents blockWidth margin) :
    M.RegionErasureRecoverable block := by sorry
