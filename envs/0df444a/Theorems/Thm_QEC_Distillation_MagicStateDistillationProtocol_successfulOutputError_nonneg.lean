-- Prove2me | Theorems.Thm_QEC_Distillation_MagicStateDistillationProtocol_successfulOutputError_nonneg
-- name    : QEC.Distillation.MagicStateDistillationProtocol.successfulOutputError_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:36.714724+00:00
-- url     : https://prove2.me/theorems/0b9a3240-785c-4c21-8566-661d6d59a93a
-- title:
--   Magic State Distillation Protocol: successful Output Error nonneg
-- statement:
--   The Magic State Distillation Protocol construction uses the successful Output Error nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L375-L378
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L375-L378

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
open scoped BigOperators
open QEC.Distillation.MagicStateDistillationProtocol
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]

theorem QEC.Distillation.MagicStateDistillationProtocol.successfulOutputError_nonneg
    (protocol : MagicStateDistillationProtocol Resource Input Output) :
    0 ≤ protocol.successfulOutputError := by sorry
