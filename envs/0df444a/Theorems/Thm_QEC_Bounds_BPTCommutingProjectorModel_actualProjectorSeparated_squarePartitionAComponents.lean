-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_actualProjectorSeparated_squarePartitionAComponents
-- name    : QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_squarePartitionAComponents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:25:29.697651+00:00
-- url     : https://prove2.me/theorems/8d514483-fb83-41f6-975f-b05d66ac5f30
-- title:
--   BPTCommuting Projector Model: actual Projector Separated square Partition AComponents
-- statement:
--   The concrete finite `A` family satisfies #403's actual-support separation
--   premise.  This derives it from the source checkerboard and corner-cutout
--   geometry rather than accepting pairwise separation as a caller hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1473-L1497
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1473-L1497

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

theorem QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_squarePartitionAComponents
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hrangeBlock : M.interactionRange ≤ blockWidth)
    (hrangeMargin : M.interactionRange ≤ margin)
    (left : Finset L.Site)
    (hleft : left ∈ L.lattice.squarePartitionAComponents blockWidth margin)
    (right : Finset L.Site)
    (hright : right ∈ L.lattice.squarePartitionAComponents blockWidth margin)
    (hne : left ≠ right) :
    M.ActualProjectorSeparated left right := by sorry
