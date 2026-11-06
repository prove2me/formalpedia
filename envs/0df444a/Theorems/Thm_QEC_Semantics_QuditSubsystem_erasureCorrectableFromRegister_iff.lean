-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureCorrectableFromRegister_iff
-- name    : QEC.Semantics.QuditSubsystem.erasureCorrectableFromRegister_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:46:53.156599+00:00
-- url     : https://prove2.me/theorems/4bab4cd0-22ee-4ef0-98fc-25b75f54cfc8
-- title:
--   Qudit Subsystem: erasure Correctable From Register iff
-- statement:
--   Typed global qudit erasure correctability is the existing `Correctable` predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L817-L823
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L817-L823

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
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

theorem QEC.Semantics.QuditSubsystem.erasureCorrectableFromRegister_iff (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q)) :
    S.ErasureCorrectableFromRegister C recovery ↔
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister recovery := by sorry
