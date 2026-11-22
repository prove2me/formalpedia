-- Prove2me | Theorems.Thm_QEC_Distillation_bk05TCompleteSemanticSchedule_rootInput_eq_noisyInput
-- name    : QEC.Distillation.bk05TCompleteSemanticSchedule_rootInput_eq_noisyInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T21:36:17.517715+00:00
-- url     : https://prove2.me/theorems/9e5e1879-6f8f-4a36-955f-15f619d00779
-- title:
--   Distillation: bk05 TComplete Semantic Schedule root Input eq noisy Input
-- statement:
--   The Distillation construction uses the bk05 TComplete Semantic Schedule root Input eq noisy Input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L127-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L127-L142

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

theorem QEC.Distillation.bk05TCompleteSemanticSchedule_rootInput_eq_noisyInput
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    BK05TSemanticSchedule.rootInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1)) =
      (BK05T.fiveQubitDistillationRun (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth)).noisyInput := by sorry
