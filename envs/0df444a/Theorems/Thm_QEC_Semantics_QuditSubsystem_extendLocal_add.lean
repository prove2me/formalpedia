-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_add
-- name    : QEC.Semantics.QuditSubsystem.extendLocal_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:54.030881+00:00
-- url     : https://prove2.me/theorems/0b02aacb-5f14-4c41-ab4a-0438f62ebfec
-- title:
--   Qudit Subsystem: extend Local add
-- statement:
--   Factorized local extension preserves addition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L699-L703
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L699-L703

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

theorem QEC.Semantics.QuditSubsystem.extendLocal_add (S : QuditSubsystem q)
    (A B : Operator S.selectedSystem) :
    S.extendLocal (A + B) = S.extendLocal A + S.extendLocal B := by sorry
