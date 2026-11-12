-- Prove2me | Theorems.Thm_QEC_Distillation_IdealResourceUniversality_sourceTPreparationLedger_eq
-- name    : QEC.Distillation.IdealResourceUniversality.sourceTPreparationLedger_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:13:03.92912+00:00
-- url     : https://prove2.me/theorems/e98f0a8c-0d0a-4df2-86c5-abe9a9c52ac9
-- title:
--   Ideal Resource Universality: source TPreparation Ledger eq
-- statement:
--   Every repeated preparation attempt consumes exactly two fresh source-T states.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L156-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L156-L159

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

theorem QEC.Distillation.IdealResourceUniversality.sourceTPreparationLedger_eq (attemptCount : Nat) :
    sourceTPreparationLedger attemptCount =
      Multiset.replicate (2 * attemptCount) sourceTDensity := by sorry
