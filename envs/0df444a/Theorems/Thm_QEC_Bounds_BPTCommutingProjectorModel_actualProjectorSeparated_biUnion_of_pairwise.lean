-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_actualProjectorSeparated_biUnion_of_pairwise
-- name    : QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_biUnion_of_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:06.849443+00:00
-- url     : https://prove2.me/theorems/d89cdcea-6165-49bb-8ab3-dac49ae7ae34
-- title:
--   BPTCommuting Projector Model: actual Projector Separated bi Union of pairwise
-- statement:
--   Pairwise source separation extends to a single explicit block and the finite
--   union of all distinct remaining blocks.  The conclusion still speaks about
--   the concrete `M.support` predicate required by #403.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1876-L1891
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1876-L1891

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

theorem QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_biUnion_of_pairwise
    (M : BPTCommutingProjectorModel L kappa) (block : Finset L.Site)
    (blocks : Finset (Finset L.Site)) (hblock : block ∉ blocks)
    (hseparated : ∀ other ∈ blocks, block ≠ other →
      M.ActualProjectorSeparated block other) :
    M.ActualProjectorSeparated block (blocks.biUnion id) := by sorry
