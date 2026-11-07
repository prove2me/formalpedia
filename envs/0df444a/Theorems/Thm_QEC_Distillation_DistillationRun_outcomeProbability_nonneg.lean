-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationRun_outcomeProbability_nonneg
-- name    : QEC.Distillation.DistillationRun.outcomeProbability_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:58:15.119628+00:00
-- url     : https://prove2.me/theorems/15258baf-9753-4cd0-b315-dcba8e261855
-- title:
--   Distillation Run: outcome Probability nonneg
-- statement:
--   The Distillation Run construction uses the outcome Probability nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L253-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L253-L257

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

theorem QEC.Distillation.DistillationRun.outcomeProbability_nonneg
    (run : DistillationRun Resource Input Output)
    (outcome : DistillationOutcome) :
    0 ≤ run.outcomeProbability outcome := by sorry
