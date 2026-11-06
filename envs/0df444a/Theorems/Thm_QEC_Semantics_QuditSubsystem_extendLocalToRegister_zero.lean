-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_zero
-- name    : QEC.Semantics.QuditSubsystem.extendLocalToRegister_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:22.283093+00:00
-- url     : https://prove2.me/theorems/e195d059-b042-4b87-bba2-77a580f5ec07
-- title:
--   Qudit Subsystem: extend Local To Register zero
-- statement:
--   Identity extension maps the zero local operator to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L394-L398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L394-L398

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

theorem QEC.Semantics.QuditSubsystem.extendLocalToRegister_zero (S : QuditSubsystem q) :
    S.extendLocalToRegister (0 : Operator S.selectedSystem) = 0 := by sorry
