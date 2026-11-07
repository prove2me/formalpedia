-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationRun_conditionalOutput_trace
-- name    : QEC.Distillation.DistillationRun.conditionalOutput_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:58:57.392292+00:00
-- url     : https://prove2.me/theorems/0bcfed4d-3715-40d9-b090-3d1780c88355
-- title:
--   Distillation Run: conditional Output trace
-- statement:
--   The Distillation Run construction uses the conditional Output trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L275-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L275-L279

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

theorem QEC.Distillation.DistillationRun.conditionalOutput_trace
    (run : DistillationRun Resource Input Output)
    (outcome : DistillationOutcome) :
    LinearMap.trace Complex Output (run.conditionalOutput outcome).toOperator = 1 := by sorry
