-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_biUnion_of_pairwise_actualProjectorSeparated
-- name    : QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_biUnion_of_pairwise_actualProjectorSeparated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:21:37.329949+00:00
-- url     : https://prove2.me/theorems/fa9365fc-6676-4a7b-bc0c-1ed181c8ffab
-- title:
--   BPTCommuting Projector Model: region Erasure Recoverable bi Union of pairwise actual Projector Separated
-- statement:
--   The finite induction that the BPT checkerboard argument needs to recover one
--   color class.  Every induction step invokes #403 on one concrete square block
--   and the union already recovered from the remaining blocks.  Consequently this
--   lemma neither assumes a recovery for the final union nor erases the required
--   external-boundary recovery premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1900-L1949
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1900-L1949

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

theorem QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_biUnion_of_pairwise_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (blocks : Finset (Finset L.Site))
    (hnonempty : blocks.Nonempty)
    (hrecoverable : ∀ block ∈ blocks, M.RegionErasureRecoverable block)
    (hexternal : ∀ block ∈ blocks,
      M.RegionErasureRecoverable (M.externalBoundary block))
    (hseparated : ∀ left ∈ blocks, ∀ right ∈ blocks, left ≠ right →
      M.ActualProjectorSeparated left right) :
    M.RegionErasureRecoverable (blocks.biUnion id) := by sorry
