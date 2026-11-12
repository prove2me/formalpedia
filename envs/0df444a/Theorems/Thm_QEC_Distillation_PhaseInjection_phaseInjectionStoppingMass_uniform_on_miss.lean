-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionStoppingMass_uniform_on_miss
-- name    : QEC.Distillation.PhaseInjection.phaseInjectionStoppingMass_uniform_on_miss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:24:18.734252+00:00
-- url     : https://prove2.me/theorems/aa943dee-0737-41b6-9ddf-d0336eb16b3e
-- title:
--   Phase Injection: phase Injection Stopping Mass uniform on miss
-- statement:
--   The Phase Injection construction uses the phase Injection Stopping Mass uniform on miss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1446-L1460
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1446-L1460

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

theorem QEC.Distillation.PhaseInjection.phaseInjectionStoppingMass_uniform_on_miss {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.TargetMissTrace q blocks start target)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    phaseInjectionStoppingMass start target trace.1 psi hpsi =
      (1 / 2 : Real) ^ (q * blocks) := by sorry
