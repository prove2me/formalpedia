-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_zero
-- name    : QEC.Semantics.QuditSubsystem.extendLocal_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:59.726888+00:00
-- url     : https://prove2.me/theorems/ebe3d4cd-b243-4e21-bee1-30593cd6e80b
-- title:
--   Qudit Subsystem: extend Local zero
-- statement:
--   Factorized local extension maps zero to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L706-L709
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L706-L709

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

theorem QEC.Semantics.QuditSubsystem.extendLocal_zero (S : QuditSubsystem q) :
    S.extendLocal (0 : Operator S.selectedSystem) = 0 := by sorry
