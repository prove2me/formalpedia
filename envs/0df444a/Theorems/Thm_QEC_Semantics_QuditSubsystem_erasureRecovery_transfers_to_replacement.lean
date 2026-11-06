-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_transfers_to_replacement
-- name    : QEC.Semantics.QuditSubsystem.erasureRecovery_transfers_to_replacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:48:46.831713+00:00
-- url     : https://prove2.me/theorems/1f2a640d-d849-4d50-836c-f43113495e8d
-- title:
--   Qudit Subsystem: erasure Recovery transfers to replacement
-- statement:
--   The Qudit Subsystem construction uses the erasure Recovery transfers to replacement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L243-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L243-L256

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

theorem QEC.Semantics.QuditSubsystem.erasureRecovery_transfers_to_replacement (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (C : QuantumCode (Qudit.QuditRegister q))
    (erasureRecovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q)) :
    Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister erasureRecovery →
    Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
      (S.replacementAfterErasureWith rho)
      (QuantumChannel.comp erasureRecovery S.erasureChannelFromRegister) := by sorry
