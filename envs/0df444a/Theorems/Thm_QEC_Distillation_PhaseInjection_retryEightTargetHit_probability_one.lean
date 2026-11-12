-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_retryEightTargetHit_probability_one
-- name    : QEC.Distillation.PhaseInjection.retryEightTargetHit_probability_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:37:21.803047+00:00
-- url     : https://prove2.me/theorems/c8400e48-dd85-4f0b-a56a-0407249beec6
-- title:
--   Phase Injection: retry Eight Target Hit probability one
-- statement:
--   The order-eight finite retry family reaches every requested cyclic target asymptotically.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L740-L743
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L740-L743

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

theorem QEC.Distillation.PhaseInjection.retryEightTargetHit_probability_one (start target : ZMod 8) :
    Filter.Tendsto (fun blocks =>
      PhaseRetry.targetHitProbability 8 blocks start target) Filter.atTop (nhds 1) := by sorry
