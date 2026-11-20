-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_support_disjoint_intersection_of_actualProjectorSeparated
-- name    : QEC.Bounds.BPTCommutingProjectorModel.support_disjoint_intersection_of_actualProjectorSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:41.756339+00:00
-- url     : https://prove2.me/theorems/45f561ce-9b08-4aa3-b6bf-beb4abe55b34
-- title:
--   BPTCommuting Projector Model: support disjoint intersection of actual Projector Separated
-- statement:
--   No actual projector touches the overlap of source-separated regions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L42-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L42-L51

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

theorem QEC.Bounds.BPTCommutingProjectorModel.support_disjoint_intersection_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) (check : kappa) :
    Disjoint (M.support check) (left ∩ right) := by sorry
