-- Prove2me | Theorems.Thm_QEC_Distillation_bk05TCompleteSemanticSchedule_protocol_inputPermitted
-- name    : QEC.Distillation.bk05TCompleteSemanticSchedule_protocol_inputPermitted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T22:50:35.276522+00:00
-- url     : https://prove2.me/theorems/2e61b5ad-b1d0-4534-92aa-8d443e87342d
-- title:
--   Distillation: bk05 TComplete Semantic Schedule protocol input Permitted
-- statement:
--   The Distillation construction uses the bk05 TComplete Semantic Schedule protocol input Permitted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L242-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L242-L253

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

theorem QEC.Distillation.bk05TCompleteSemanticSchedule_protocol_inputPermitted
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (depth : Nat) :
    (BK05T.fiveQubitMagicStateProtocol (tIteration rho depth)
      (tIteration_bounds rho hthreshold depth).1
      (tIteration_le_one rho hthreshold depth)).inputErrorModel.Permits
      (BK05TSemanticSchedule.rootInput
        (bk05TCompleteSemanticSchedule rho hthreshold (depth + 1))) := by sorry
