-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_retryTraceCoins_length
-- name    : QEC.Distillation.PhaseInjection.retryTraceCoins_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:20:40.565149+00:00
-- url     : https://prove2.me/theorems/dd566bb1-8766-4e47-80d7-65d6c7d58632
-- title:
--   Phase Injection: retry Trace Coins length
-- statement:
--   The Phase Injection construction uses the retry Trace Coins length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1298-L1305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1298-L1305

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

theorem QEC.Distillation.PhaseInjection.retryTraceCoins_length {q blocks : Nat} (trace : PhaseRetry.BlockTrace q blocks) :
    (retryTraceCoins blocks trace).length = q * blocks := by sorry
