-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionTrace_output
-- name    : QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_output
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:21:25.450667+00:00
-- url     : https://prove2.me/theorems/9f6fec93-e082-4e37-95cc-13e303e8a524
-- title:
--   Phase Injection: repeated Phase Injection Trace output
-- statement:
--   The state component of the resource trace is the existing recursive circuit execution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L900-L909
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L900-L909

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

theorem QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_output (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionTrace theta coins psi hpsi).1 =
      repeatedPhaseInjection theta coins psi hpsi := by sorry
