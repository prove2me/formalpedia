-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannelFromRegister_specification
-- name    : QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_specification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:46:25.911521+00:00
-- url     : https://prove2.me/theorems/062ff0f0-80dd-4d64-b925-f64903de2064
-- title:
--   Qudit Subsystem: erasure Channel From Register specification
-- statement:
--   The global erasure channel is exactly coordinate factorization followed by factored erasure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L479-L483
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L479-L483

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

theorem QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_specification (S : QuditSubsystem q) :
    S.erasureChannelFromRegister =
      QuantumChannel.comp S.erasureChannel
        (QuantumChannel.unitaryConj S.registerFactorization) := by sorry
