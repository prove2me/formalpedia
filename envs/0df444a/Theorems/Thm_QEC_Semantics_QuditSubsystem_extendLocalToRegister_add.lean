-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_add
-- name    : QEC.Semantics.QuditSubsystem.extendLocalToRegister_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:37.539192+00:00
-- url     : https://prove2.me/theorems/faa5d806-bbbc-4fba-8e9d-39b529fbc46d
-- title:
--   Qudit Subsystem: extend Local To Register add
-- statement:
--   Identity extension preserves local operator addition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L384-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L384-L391

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

theorem QEC.Semantics.QuditSubsystem.extendLocalToRegister_add (S : QuditSubsystem q)
    (A B : Operator S.selectedSystem) :
    S.extendLocalToRegister (A + B) =
      S.extendLocalToRegister A + S.extendLocalToRegister B := by sorry
