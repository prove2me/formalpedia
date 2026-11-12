-- Prove2me | Theorems.Thm_QEC_Distillation_IdealResourceUniversality_hResource_projectivelyGeneratedDense
-- name    : QEC.Distillation.IdealResourceUniversality.hResource_projectivelyGeneratedDense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:08:50.164963+00:00
-- url     : https://prove2.me/theorems/96ea5057-4497-4d67-b6fa-88746b652d3c
-- title:
--   Ideal Resource Universality: h Resource projectively Generated Dense
-- statement:
--   The already-constructed H-route words give projective generated density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L72-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L72-L80

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

theorem QEC.Distillation.IdealResourceUniversality.hResource_projectivelyGeneratedDense :
    ProjectivelyGeneratedDense hResourceGenerators := by sorry
