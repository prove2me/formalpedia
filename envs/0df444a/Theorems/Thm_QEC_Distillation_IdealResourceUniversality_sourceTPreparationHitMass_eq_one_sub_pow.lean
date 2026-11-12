-- Prove2me | Theorems.Thm_QEC_Distillation_IdealResourceUniversality_sourceTPreparationHitMass_eq_one_sub_pow
-- name    : QEC.Distillation.IdealResourceUniversality.sourceTPreparationHitMass_eq_one_sub_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:08:44.35514+00:00
-- url     : https://prove2.me/theorems/60f5ba3f-7488-4de9-8e29-1e0851005bba
-- title:
--   Ideal Resource Universality: source TPreparation Hit Mass eq one sub pow
-- statement:
--   The finite fresh-pair preparation mass has the exact geometric form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L170-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L170-L179

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

theorem QEC.Distillation.IdealResourceUniversality.sourceTPreparationHitMass_eq_one_sub_pow (attemptBudget : Nat) :
    sourceTPreparationHitMass attemptBudget =
      1 - (1 / 3 : Real) ^ attemptBudget := by sorry
