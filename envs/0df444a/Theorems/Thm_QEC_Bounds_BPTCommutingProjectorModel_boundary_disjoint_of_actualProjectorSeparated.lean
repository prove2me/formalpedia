-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_disjoint_of_actualProjectorSeparated
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundary_disjoint_of_actualProjectorSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:17.688608+00:00
-- url     : https://prove2.me/theorems/6be97dc2-59ff-4e73-b78b-028c6f08f1c6
-- title:
--   BPTCommuting Projector Model: boundary disjoint of actual Projector Separated
-- statement:
--   The actual source boundary of the left region is disjoint from the right region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L168-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L168-L179

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundary_disjoint_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    Disjoint (M.boundary left) right := by sorry
