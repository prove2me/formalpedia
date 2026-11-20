-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_actualProjectorSeparated_squarePartitionBComponents
-- name    : QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_squarePartitionBComponents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:25:46.821991+00:00
-- url     : https://prove2.me/theorems/1a02a36c-53d2-40fb-8fa7-f4e76e69c92a
-- title:
--   BPTCommuting Projector Model: actual Projector Separated square Partition BComponents
-- statement:
--   The matching actual-support separation theorem for the finite `B` family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1500-L1524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1500-L1524

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

theorem QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_squarePartitionBComponents
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (left : Finset L.Site)
    (hleft : left ∈ L.lattice.squarePartitionBComponents blockWidth margin)
    (right : Finset L.Site)
    (hright : right ∈ L.lattice.squarePartitionBComponents blockWidth margin)
    (hne : left ≠ right) :
    M.ActualProjectorSeparated left right := by sorry
