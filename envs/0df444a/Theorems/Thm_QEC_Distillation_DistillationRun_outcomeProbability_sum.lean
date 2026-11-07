-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationRun_outcomeProbability_sum
-- name    : QEC.Distillation.DistillationRun.outcomeProbability_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:58:36.606682+00:00
-- url     : https://prove2.me/theorems/91967189-18eb-4276-ab78-3bf9833780b3
-- title:
--   Distillation Run: outcome Probability sum
-- statement:
--   The Distillation Run construction uses the outcome Probability sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L259-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L259-L261

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
open scoped BigOperators
open QEC.Distillation.DistillationRun
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]

theorem QEC.Distillation.DistillationRun.outcomeProbability_sum (run : DistillationRun Resource Input Output) :
    run.outcomeProbability .accepted + run.outcomeProbability .rejected = 1 := by sorry
