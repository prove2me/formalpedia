-- Prove2me | Theorems.Thm_QEC_Distillation_bk05TCompleteSemanticSchedule_preparedInput_eq_run_preparedInput
-- name    : QEC.Distillation.bk05TCompleteSemanticSchedule_preparedInput_eq_run_preparedInput
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T21:36:16.98953+00:00
-- url     : https://prove2.me/theorems/bcddb7f5-0cc7-475a-add8-539045f9d03f
-- title:
--   Distillation: bk05 TComplete Semantic Schedule prepared Input eq run prepared Input
-- statement:
--   The Distillation construction uses the bk05 TComplete Semantic Schedule prepared Input eq run prepared Input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L144-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L144-L162

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

theorem QEC.Distillation.bk05TCompleteSemanticSchedule_preparedInput_eq_run_preparedInput
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    BK05TSemanticSchedule.preparedInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).prepareInput
        ((BK05T.fiveQubitDistillationRun (tIteration rho depth)
          (tIteration_bounds rho hthreshold depth).1
          (tIteration_le_one rho hthreshold depth)).noisyInput) := by sorry
