-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_squarePartitionA_regionErasureRecoverable_of_components
-- name    : QEC.Bounds.BPTCommutingProjectorModel.squarePartitionA_regionErasureRecoverable_of_components
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:27:13.292193+00:00
-- url     : https://prove2.me/theorems/3bdebeb6-36d5-44f7-bd56-707c4861e00f
-- title:
--   BPTCommuting Projector Model: square Partition A region Erasure Recoverable of components
-- statement:
--   The explicit finite `A` partition is recoverable once its individually seeded
--   components have their actual external-boundary recoveries and pairwise
--   actual-projector separation.  The result is an exact #403 iteration, not a
--   whole-region recovery hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1957-L1971
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1957-L1971

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

theorem QEC.Bounds.BPTCommutingProjectorModel.squarePartitionA_regionErasureRecoverable_of_components
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hnonempty : (L.lattice.squarePartitionAComponents blockWidth margin).Nonempty)
    (hrecoverable : ∀ block ∈ L.lattice.squarePartitionAComponents blockWidth margin,
      M.RegionErasureRecoverable block)
    (hexternal : ∀ block ∈ L.lattice.squarePartitionAComponents blockWidth margin,
      M.RegionErasureRecoverable (M.externalBoundary block))
    (hseparated : ∀ left ∈ L.lattice.squarePartitionAComponents blockWidth margin,
      ∀ right ∈ L.lattice.squarePartitionAComponents blockWidth margin, left ≠ right →
        M.ActualProjectorSeparated left right) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin) := by sorry
