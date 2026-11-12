-- Prove2me | Theorems.Thm_QEC_Distillation_IdealResourceUniversality_tResource_projectivelyGeneratedDense
-- name    : QEC.Distillation.IdealResourceUniversality.tResource_projectivelyGeneratedDense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:08:29.841042+00:00
-- url     : https://prove2.me/theorems/df7d8e4d-e07f-4b01-893f-555746e93b2f
-- title:
--   Ideal Resource Universality: t Resource projectively Generated Dense
-- statement:
--   The already-constructed T-route words give projective generated density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L83-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L83-L92

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

theorem QEC.Distillation.IdealResourceUniversality.tResource_projectivelyGeneratedDense :
    ProjectivelyGeneratedDense tResourceGenerators := by sorry
