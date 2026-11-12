-- Prove2me | Theorems.Thm_QEC_Distillation_IdealResourceUniversality_hResource_stoppingOutputDensity_target
-- name    : QEC.Distillation.IdealResourceUniversality.hResource_stoppingOutputDensity_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:13:00.970815+00:00
-- url     : https://prove2.me/theorems/ffae35b9-72eb-48ec-af97-4345a50448e9
-- title:
--   Ideal Resource Universality: h Resource stopping Output Density target
-- statement:
--   A visited H-route block trace has the exact target output density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L271-L281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L271-L281

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

theorem QEC.Distillation.IdealResourceUniversality.hResource_stoppingOutputDensity_target {blocks : Nat}
    (trace : PhaseRetry.BlockTrace 8 blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.traceVisitsTarget
      (0 : ZMod 8) (1 : ZMod 8) blocks trace) :
    phaseInjectionStoppingOutputDensity
        (0 : ZMod 8) (1 : ZMod 8) trace psi hpsi =
      phaseCycleTargetOutputDensity 8 (1 : ZMod 8) psi hpsi := by sorry
