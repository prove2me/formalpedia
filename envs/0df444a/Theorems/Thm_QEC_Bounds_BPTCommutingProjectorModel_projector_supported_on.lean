-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projector_supported_on
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projector_supported_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:32:54.696198+00:00
-- url     : https://prove2.me/theorems/7f733907-0fc6-4f6e-87b3-19b1c60a9dec
-- title:
--   BPTCommuting Projector Model: projector supported on
-- statement:
--   Each actual projector is explicitly supported on its recorded finite site set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L165-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L165-L168

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projector_supported_on (M : BPTCommutingProjectorModel L κ) (check : κ) :
    (L.subsystem (M.support check)).OperatorSupportedOnRegister (M.projector check) := by sorry
