-- Prove2me | Theorems.Thm_QEC_Distillation_IdealResourceUniversality_sourceTPreparationHitMass_add_missMass
-- name    : QEC.Distillation.IdealResourceUniversality.sourceTPreparationHitMass_add_missMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:13:36.163504+00:00
-- url     : https://prove2.me/theorems/7b3d16c5-5464-440f-ad11-bd1dbc3e01e7
-- title:
--   Ideal Resource Universality: source TPreparation Hit Mass add miss Mass
-- statement:
--   Accepted mass and the all-rejected tail exhaust the finite preparation tree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L191-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L191-L196

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

theorem QEC.Distillation.IdealResourceUniversality.sourceTPreparationHitMass_add_missMass (attemptBudget : Nat) :
    sourceTPreparationHitMass attemptBudget +
      sourceTPreparationMissMass attemptBudget = 1 := by sorry
