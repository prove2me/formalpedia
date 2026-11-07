-- Prove2me | Theorems.Thm_QEC_Distillation_MagicStateDistillationProtocol_reportedOutputError_nonneg
-- name    : QEC.Distillation.MagicStateDistillationProtocol.reportedOutputError_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:59:04.617308+00:00
-- url     : https://prove2.me/theorems/984c17a5-6a65-462f-b6f0-6037adc88b41
-- title:
--   Magic State Distillation Protocol: reported Output Error nonneg
-- statement:
--   The Magic State Distillation Protocol construction uses the reported Output Error nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L380-L383
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L380-L383

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

theorem QEC.Distillation.MagicStateDistillationProtocol.reportedOutputError_nonneg
    (protocol : MagicStateDistillationProtocol Resource Input Output) :
    0 ≤ protocol.reportedOutputError := by sorry
