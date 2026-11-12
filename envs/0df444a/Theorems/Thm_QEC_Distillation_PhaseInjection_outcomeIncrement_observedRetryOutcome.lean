-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_outcomeIncrement_observedRetryOutcome
-- name    : QEC.Distillation.PhaseInjection.outcomeIncrement_observedRetryOutcome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:15:36.753065+00:00
-- url     : https://prove2.me/theorems/011951f5-8c44-491d-8604-a05e0aa3f737
-- title:
--   Phase Injection: outcome Increment observed Retry Outcome
-- statement:
--   The observed parity label has exactly the increment used by \`PhaseRetry\`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L710-L713
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L710-L713

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

theorem QEC.Distillation.PhaseInjection.outcomeIncrement_observedRetryOutcome {q : Nat} (coin : Bool) :
    outcomeIncrement (q := q) (observedRetryOutcome coin) =
      PhaseRetry.signedIncrement (q := q) coin := by sorry
