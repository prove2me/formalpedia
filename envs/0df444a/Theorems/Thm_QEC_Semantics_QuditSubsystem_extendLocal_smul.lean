-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_smul
-- name    : QEC.Semantics.QuditSubsystem.extendLocal_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:29:37.77622+00:00
-- url     : https://prove2.me/theorems/6ff54ec4-d7f7-4e27-b3b2-50d27edccd20
-- title:
--   Qudit Subsystem: extend Local smul
-- statement:
--   Factorized local extension is complex-linear in the selected operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L692-L696
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L692-L696

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

theorem QEC.Semantics.QuditSubsystem.extendLocal_smul (S : QuditSubsystem q) (a : Complex)
    (A : Operator S.selectedSystem) :
    S.extendLocal (a • A) = a • S.extendLocal A := by sorry
