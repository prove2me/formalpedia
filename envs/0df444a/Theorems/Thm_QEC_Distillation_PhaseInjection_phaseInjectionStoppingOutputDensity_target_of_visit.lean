-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionStoppingOutputDensity_target_of_visit
-- name    : QEC.Distillation.PhaseInjection.phaseInjectionStoppingOutputDensity_target_of_visit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T15:02:18.2273+00:00
-- url     : https://prove2.me/theorems/9dfd7d46-df10-40a7-88c3-95db7754673b
-- title:
--   Phase Injection: phase Injection Stopping Output Density target of visit
-- statement:
--   On every actual hit trace, the stopped physical channel has exactly the target output density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1657-L1673
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1657-L1673

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

theorem QEC.Distillation.PhaseInjection.phaseInjectionStoppingOutputDensity_target_of_visit {q blocks : Nat} [NeZero q]
    (target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.traceVisitsTarget (0 : ZMod q) target blocks trace) :
    phaseInjectionStoppingOutputDensity (0 : ZMod q) target trace psi hpsi =
      sourceInputDensity (phaseCycleTargetAction q target psi)
        (phaseCycleTargetAction_norm q target psi hpsi) := by sorry
