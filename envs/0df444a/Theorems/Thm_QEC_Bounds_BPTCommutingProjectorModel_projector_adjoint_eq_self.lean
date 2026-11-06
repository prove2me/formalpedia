-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projector_adjoint_eq_self
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projector_adjoint_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:38:46.815687+00:00
-- url     : https://prove2.me/theorems/29a0fb8a-a08a-49f3-8e33-9127a0763973
-- title:
--   BPTCommuting Projector Model: projector adjoint eq self
-- statement:
--   The actual global projectors satisfy their supplied self-adjointness law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L181-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L181-L183

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]

theorem QEC.Bounds.BPTCommutingProjectorModel.projector_adjoint_eq_self (M : BPTCommutingProjectorModel L κ) (check : κ) :
    LinearMap.adjoint (M.projector check) = M.projector check := by sorry
