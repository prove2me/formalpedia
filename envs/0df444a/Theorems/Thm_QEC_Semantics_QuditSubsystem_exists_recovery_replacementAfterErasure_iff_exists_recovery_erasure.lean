-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_exists_recovery_replacementAfterErasure_iff_exists_recovery_erasure
-- name    : QEC.Semantics.QuditSubsystem.exists_recovery_replacementAfterErasure_iff_exists_recovery_erasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:16:36.937966+00:00
-- url     : https://prove2.me/theorems/58e01a1a-2e14-41cc-b17c-e5b12b367cbd
-- title:
--   Qudit Subsystem: exists recovery replacement After Erasure iff exists recovery erasure
-- statement:
--   The Qudit Subsystem construction uses the exists recovery replacement After Erasure iff exists recovery erasure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L275-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L275-L286

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

theorem QEC.Semantics.QuditSubsystem.exists_recovery_replacementAfterErasure_iff_exists_recovery_erasure
    (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (C : QuantumCode (Qudit.QuditRegister q)) :
    (∃ replacementRecovery : QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) (Qudit.QuditRegister q) C
        (S.replacementAfterErasure hq) replacementRecovery) ↔
    (∃ erasureRecovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
      Correctable (Qudit.QuditRegister q) S.complementSystem C
        S.erasureChannelFromRegister erasureRecovery) := by sorry
