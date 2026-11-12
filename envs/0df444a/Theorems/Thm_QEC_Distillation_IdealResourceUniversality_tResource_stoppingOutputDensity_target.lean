-- Prove2me | Theorems.Thm_QEC_Distillation_IdealResourceUniversality_tResource_stoppingOutputDensity_target
-- name    : QEC.Distillation.IdealResourceUniversality.tResource_stoppingOutputDensity_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:13:29.194915+00:00
-- url     : https://prove2.me/theorems/181b8e52-4809-4e53-932e-d602bf2db484
-- title:
--   Ideal Resource Universality: t Resource stopping Output Density target
-- statement:
--   A visited T-route block trace has the exact target output density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L284-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L284-L294

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.IdealResourceUniversality
open QEC.Semantics
open QEC.Semantics.Qubit
open GeneratedUniversality
open OneQubitMagic
open PhaseInjection
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators

theorem QEC.Distillation.IdealResourceUniversality.tResource_stoppingOutputDensity_target {blocks : Nat}
    (trace : PhaseRetry.BlockTrace 12 blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.traceVisitsTarget
      (0 : ZMod 12) (1 : ZMod 12) blocks trace) :
    phaseInjectionStoppingOutputDensity
        (0 : ZMod 12) (1 : ZMod 12) trace psi hpsi =
      phaseCycleTargetOutputDensity 12 (1 : ZMod 12) psi hpsi := by sorry
