-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProduct_adjoint_eq_self
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_adjoint_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:32:54.757268+00:00
-- url     : https://prove2.me/theorems/9b4fe965-e473-4f46-993a-5bbb280f5ddd
-- title:
--   BPTCommuting Projector Model: projector Product adjoint eq self
-- statement:
--   The source-style finite product is self-adjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L335-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L335-L338

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_adjoint_eq_self (M : BPTCommutingProjectorModel L κ) :
    LinearMap.adjoint M.projectorProduct = M.projectorProduct := by sorry
