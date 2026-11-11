-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionStoppingMissMass_eq_targetMissProbability
-- name    : QEC.Distillation.PhaseInjection.phaseInjectionStoppingMissMass_eq_targetMissProbability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:19:10.328733+00:00
-- url     : https://prove2.me/theorems/51a4a7a5-846c-4213-b7a0-8c3287c5647a
-- title:
--   Phase Injection: phase Injection Stopping Miss Mass eq target Miss Probability
-- statement:
--   The physical finite miss event has exactly the retry-calculus miss probability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1467-L1484
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1467-L1484

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

theorem QEC.Distillation.PhaseInjection.phaseInjectionStoppingMissMass_eq_targetMissProbability {q blocks : Nat}
    (start target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    phaseInjectionStoppingMissMass (blocks := blocks) start target psi hpsi =
      PhaseRetry.targetMissProbability q blocks start target := by sorry
