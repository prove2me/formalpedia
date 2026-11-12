-- Prove2me | Theorems.Thm_QEC_Distillation_IdealResourceUniversality_SourceTPreparationAcceptedTrace_ledger_eq
-- name    : QEC.Distillation.IdealResourceUniversality.SourceTPreparationAcceptedTrace.ledger_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:12:49.091406+00:00
-- url     : https://prove2.me/theorems/47bf4c90-7643-4eb4-b76c-1f728095a5cf
-- title:
--   Source TPreparation Accepted Trace: ledger eq
-- statement:
--   The trace ledger contains two fresh source-T states per actual attempt.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L144-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L144-L146

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

theorem QEC.Distillation.IdealResourceUniversality.SourceTPreparationAcceptedTrace.ledger_eq (trace : SourceTPreparationAcceptedTrace) :
    trace.ledger = Multiset.replicate (2 * trace.attemptCount) sourceTDensity := by sorry
