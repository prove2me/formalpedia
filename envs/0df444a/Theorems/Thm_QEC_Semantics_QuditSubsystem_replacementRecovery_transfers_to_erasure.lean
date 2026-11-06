-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementRecovery_transfers_to_erasure
-- name    : QEC.Semantics.QuditSubsystem.replacementRecovery_transfers_to_erasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:48:44.926896+00:00
-- url     : https://prove2.me/theorems/8200d3f5-41f7-4511-a5d1-82c87496a134
-- title:
--   Qudit Subsystem: replacement Recovery transfers to erasure
-- statement:
--   The Qudit Subsystem construction uses the replacement Recovery transfers to erasure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L229-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L229-L241

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

theorem QEC.Semantics.QuditSubsystem.replacementRecovery_transfers_to_erasure (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (C : QuantumCode (Qudit.QuditRegister q))
    (replacementRecovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q)) :
    Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
      (S.replacementAfterErasureWith rho) replacementRecovery →
    Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister
      (QuantumChannel.comp replacementRecovery (S.prepareSelected rho)) := by sorry
