-- Prove2me | Theorems.Thm_QEC_Distillation_DistillationRun_rawOutput_eq_outcomeMixture
-- name    : QEC.Distillation.DistillationRun.rawOutput_eq_outcomeMixture
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:58:46.44376+00:00
-- url     : https://prove2.me/theorems/4b059e3d-36bd-444b-a015-8dc455c50321
-- title:
--   Distillation Run: raw Output eq outcome Mixture
-- statement:
--   The Distillation Run construction uses the raw Output eq outcome Mixture property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L281-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/MagicStateProtocol.lean#L281-L286

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

theorem QEC.Distillation.DistillationRun.rawOutput_eq_outcomeMixture
    (run : DistillationRun Resource Input Output) :
    run.rawOutput =
      outcomeMixture run.successProbability run.success_nonneg run.success_le_one
        run.acceptedOutput run.rejectedOutput := by sorry
