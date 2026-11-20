-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_squarePartitionB_regionErasureRecoverable_of_components
-- name    : QEC.Bounds.BPTCommutingProjectorModel.squarePartitionB_regionErasureRecoverable_of_components
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:26:50.626389+00:00
-- url     : https://prove2.me/theorems/2f8d4d1d-3ac0-41df-bc40-63e32f13767b
-- title:
--   BPTCommuting Projector Model: square Partition B region Erasure Recoverable of components
-- statement:
--   The matching finite #403 assembly for the explicit `B` component family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1974-L1988
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1974-L1988

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

theorem QEC.Bounds.BPTCommutingProjectorModel.squarePartitionB_regionErasureRecoverable_of_components
    (M : BPTCommutingProjectorModel L kappa) {blockWidth : Nat}
    (hblockWidth : 0 < blockWidth) (margin : Nat)
    (hnonempty : (L.lattice.squarePartitionBComponents blockWidth margin).Nonempty)
    (hrecoverable : ∀ block ∈ L.lattice.squarePartitionBComponents blockWidth margin,
      M.RegionErasureRecoverable block)
    (hexternal : ∀ block ∈ L.lattice.squarePartitionBComponents blockWidth margin,
      M.RegionErasureRecoverable (M.externalBoundary block))
    (hseparated : ∀ left ∈ L.lattice.squarePartitionBComponents blockWidth margin,
      ∀ right ∈ L.lattice.squarePartitionBComponents blockWidth margin, left ≠ right →
        M.ActualProjectorSeparated left right) :
    M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin) := by sorry
