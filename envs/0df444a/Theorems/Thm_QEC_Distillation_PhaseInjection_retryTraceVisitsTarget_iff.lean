-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_retryTraceVisitsTarget_iff
-- name    : QEC.Distillation.PhaseInjection.retryTraceVisitsTarget_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:20:25.784934+00:00
-- url     : https://prove2.me/theorems/04958eb9-3916-4670-9a27-8888275a687a
-- title:
--   Phase Injection: retry Trace Visits Target iff
-- statement:
--   The Phase Injection construction uses the retry Trace Visits Target iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1393-L1411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1393-L1411

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

theorem QEC.Distillation.PhaseInjection.retryTraceVisitsTarget_iff {q blocks : Nat} (start target : ZMod q)
    (trace : PhaseRetry.BlockTrace q blocks) :
    PhaseRetry.traceVisitsTarget start target blocks trace ↔
      PhaseRetry.visitsTarget start target (retryTraceCoins blocks trace) := by sorry
