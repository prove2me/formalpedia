-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProduct_eq_fullCodeProjector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_eq_fullCodeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:33:00.088662+00:00
-- url     : https://prove2.me/theorems/21791219-9d8e-4c44-aefc-b0b398db72d2
-- title:
--   BPTCommuting Projector Model: projector Product eq full Code Projector
-- statement:
--   The constructed full projector equals the finite product of actual projectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L347-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L347-L373

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_eq_fullCodeProjector (M : BPTCommutingProjectorModel L κ) :
    M.projectorProduct = M.fullCodeProjector := by sorry
