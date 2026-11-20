-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_sdiff_right_eq_of_actualProjectorSeparated
-- name    : QEC.Bounds.BPTCommutingProjectorModel.boundary_sdiff_right_eq_of_actualProjectorSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:35.33263+00:00
-- url     : https://prove2.me/theorems/7c193b37-38a5-4084-94d7-17d368c5ba92
-- title:
--   BPTCommuting Projector Model: boundary sdiff right eq of actual Projector Separated
-- statement:
--   Actual separation preserves the literal source boundary after normalization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L95-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Separation.lean#L95-L111

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

theorem QEC.Bounds.BPTCommutingProjectorModel.boundary_sdiff_right_eq_of_actualProjectorSeparated
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    M.boundary (left \ right) = M.boundary left := by sorry
