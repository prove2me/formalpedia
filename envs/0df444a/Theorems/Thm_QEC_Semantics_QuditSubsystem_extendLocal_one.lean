-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_one
-- name    : QEC.Semantics.QuditSubsystem.extendLocal_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:08.004989+00:00
-- url     : https://prove2.me/theorems/58699138-6543-4564-816e-2e384a6b839e
-- title:
--   Qudit Subsystem: extend Local one
-- statement:
--   Extending the local identity is the factorized identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L722-L729
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L722-L729

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

theorem QEC.Semantics.QuditSubsystem.extendLocal_one (S : QuditSubsystem q) :
    S.extendLocal (1 : Operator S.selectedSystem) = 1 := by sorry
