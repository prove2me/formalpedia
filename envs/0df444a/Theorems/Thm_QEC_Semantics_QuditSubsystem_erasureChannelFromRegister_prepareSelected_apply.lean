-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannelFromRegister_prepareSelected_apply
-- name    : QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_prepareSelected_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:48:34.665035+00:00
-- url     : https://prove2.me/theorems/7c4348e7-dc6c-48dd-bf5d-922da7e36d80
-- title:
--   Qudit Subsystem: erasure Channel From Register prepare Selected apply
-- statement:
--   The Qudit Subsystem construction uses the erasure Channel From Register prepare Selected apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L212-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L212-L218

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_prepareSelected_apply (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (A : Operator S.complementSystem) :
    S.erasureChannelFromRegister (S.prepareSelected rho A) = A := by sorry
