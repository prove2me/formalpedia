-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannelFromRegister_comp_prepareSelected
-- name    : QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_comp_prepareSelected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:16:18.059202+00:00
-- url     : https://prove2.me/theorems/18333ba9-b568-4110-9a8f-936b4348ff04
-- title:
--   Qudit Subsystem: erasure Channel From Register comp prepare Selected
-- statement:
--   The Qudit Subsystem construction uses the erasure Channel From Register comp prepare Selected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L220-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean#L220-L227

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

theorem QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_comp_prepareSelected (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    QuantumChannel.comp S.erasureChannelFromRegister (S.prepareSelected rho) =
      QuantumChannel.id S.complementSystem := by sorry
