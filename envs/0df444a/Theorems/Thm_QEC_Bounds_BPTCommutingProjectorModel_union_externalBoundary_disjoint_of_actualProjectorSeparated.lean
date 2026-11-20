-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_union_externalBoundary_disjoint_of_actualProjectorSeparated
-- name    : QEC.Bounds.BPTCommutingProjectorModel.union_externalBoundary_disjoint_of_actualProjectorSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:19:44.380708+00:00
-- url     : https://prove2.me/theorems/bede5974-0f6d-43e9-ad7c-3f4c416335cf
-- title:
--   BPTCommuting Projector Model: union external Boundary disjoint of actual Projector Separated
-- statement:
--   Actual-projector separation leaves the right region outside both the left
--   region and its external boundary, namely in the source exterior `D`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L196-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L196-L203

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.union_externalBoundary_disjoint_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right) :
    Disjoint (left ∪ M.externalBoundary left) right := by sorry
