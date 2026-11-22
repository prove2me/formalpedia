-- Prove2me | Theorems.Thm_QEC_Distillation_bk05TCompleteSemanticSchedule_rootOutput_eq_run_acceptedOutput
-- name    : QEC.Distillation.bk05TCompleteSemanticSchedule_rootOutput_eq_run_acceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T22:49:45.346012+00:00
-- url     : https://prove2.me/theorems/7df9af7c-f8c8-47b1-9933-fc0017df6d88
-- title:
--   Distillation: bk05 TComplete Semantic Schedule root Output eq run accepted Output
-- statement:
--   The Distillation construction uses the bk05 TComplete Semantic Schedule root Output eq run accepted Output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L164-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L164-L178

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_MagicStateThreshold_Universality
set_option autoImplicit false
noncomputable section
universe u v
open QEC
open QEC.Distillation
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open GeneratedUniversality
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators Matrix.Norms.Elementwise

theorem QEC.Distillation.bk05TCompleteSemanticSchedule_rootOutput_eq_run_acceptedOutput
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    BK05TSemanticSchedule.rootOutput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).acceptedOutput := by sorry
