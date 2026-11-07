-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
-- name    : QEC.Distillation.DistillationRun.postprocess_conditionalOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:15:01.2278+00:00
-- url     : https://prove2.me/theorems/3d25bd77-1a5b-4ff9-948b-e0c2b14a73a9
-- title:
--   Distillation Run: postprocess conditional Output
-- statement:
--   The Distillation Run construction uses the postprocess conditional Output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L484-L492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L484-L492

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
set_option autoImplicit false
universe u
open QEC
open QEC.Distillation
open Semantics
open QEC.Distillation.DistillationRun
variable {Resource Input Output : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
variable [NormedAddCommGroup Input] [InnerProductSpace Complex Input]
variable [FiniteQuantumSystem Input]
variable [NormedAddCommGroup Output] [InnerProductSpace Complex Output]
variable [FiniteQuantumSystem Output]

theorem QEC.Distillation.DistillationRun.postprocess_conditionalOutput {Output' : Type u}
    [NormedAddCommGroup Output'] [InnerProductSpace Complex Output']
    [FiniteQuantumSystem Output']
    (run : DistillationRun Resource Input Output)
    (channel : QuantumChannel Output Output')
    (outcome : DistillationOutcome) :
    (run.postprocess channel).conditionalOutput outcome =
      channel.mapDensity (run.conditionalOutput outcome) := by sorry
