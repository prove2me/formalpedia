-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_smul
-- name    : QEC.Semantics.QuditSubsystem.extendLocalToRegister_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:39.574548+00:00
-- url     : https://prove2.me/theorems/41a09a77-3fe2-4dbb-b899-ca61f5a69db0
-- title:
--   Qudit Subsystem: extend Local To Register smul
-- statement:
--   Identity extension is complex-linear in the local operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L375-L381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L375-L381

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.extendLocalToRegister_smul (S : QuditSubsystem q) (a : Complex)
    (A : Operator S.selectedSystem) :
    S.extendLocalToRegister (a • A) = a • S.extendLocalToRegister A := by sorry
