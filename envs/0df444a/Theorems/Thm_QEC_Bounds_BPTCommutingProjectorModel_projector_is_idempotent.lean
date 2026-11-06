-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projector_is_idempotent
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projector_is_idempotent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:09:44.222723+00:00
-- url     : https://prove2.me/theorems/f9cb867f-f1cb-4850-a4d6-79a25566401f
-- title:
--   BPTCommuting Projector Model: projector is idempotent
-- statement:
--   The actual global projectors satisfy their supplied idempotence law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L176-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L176-L178

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projector_is_idempotent (M : BPTCommutingProjectorModel L κ) (check : κ) :
    (M.projector check).comp (M.projector check) = M.projector check := by sorry
