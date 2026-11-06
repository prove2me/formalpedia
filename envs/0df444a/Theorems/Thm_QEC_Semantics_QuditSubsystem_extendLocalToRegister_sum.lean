-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_sum
-- name    : QEC.Semantics.QuditSubsystem.extendLocalToRegister_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:50:12.723813+00:00
-- url     : https://prove2.me/theorems/985ae317-1466-428c-9f6c-bde848e92c38
-- title:
--   Qudit Subsystem: extend Local To Register sum
-- statement:
--   Identity extension preserves finite sums of local operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L401-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L401-L418

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

theorem QEC.Semantics.QuditSubsystem.extendLocalToRegister_sum (S : QuditSubsystem q) {κ : Type v}
    (s : Finset κ) (f : κ → Operator S.selectedSystem) :
    S.extendLocalToRegister (∑ i ∈ s, f i) = ∑ i ∈ s, S.extendLocalToRegister (f i) := by sorry
