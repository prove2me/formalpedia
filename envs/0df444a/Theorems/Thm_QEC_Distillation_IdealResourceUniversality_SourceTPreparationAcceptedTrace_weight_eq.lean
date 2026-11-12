-- Prove2me | Theorems.Thm_QEC_Distillation_IdealResourceUniversality_SourceTPreparationAcceptedTrace_weight_eq
-- name    : QEC.Distillation.IdealResourceUniversality.SourceTPreparationAcceptedTrace.weight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:08:26.480373+00:00
-- url     : https://prove2.me/theorems/4f28030d-9b09-4c16-848d-d7cb6f41bac3
-- title:
--   Source TPreparation Accepted Trace: weight eq
-- statement:
--   The exact geometric weight of an accepted trace after its rejections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L139-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L139-L141

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
open QEC.Distillation.IdealResourceUniversality.SourceTPreparationAcceptedTrace

theorem QEC.Distillation.IdealResourceUniversality.SourceTPreparationAcceptedTrace.weight_eq (trace : SourceTPreparationAcceptedTrace) :
    trace.weight = (1 / 3 : Real) ^ trace.rejectedAttempts * (2 / 3) := by sorry
