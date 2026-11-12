-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseEightTargetAction_eq
-- name    : QEC.Distillation.PhaseInjection.phaseEightTargetAction_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:13:15.269202+00:00
-- url     : https://prove2.me/theorems/b2931778-ba79-4885-920b-4ee12276edfd
-- title:
--   Phase Injection: phase Eight Target Action eq
-- statement:
--   The Phase Injection construction uses the phase Eight Target Action eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1153-L1156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1153-L1156

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct

theorem QEC.Distillation.PhaseInjection.phaseEightTargetAction_eq (target : ZMod 8) :
    phaseEightTargetAction target =
      OneQubitMagic.phaseShiftOperator ((-Real.pi / 4) * target.val) := by sorry
