-- Prove2me | Theorems.Thm_QEC_Distillation_IdealResourceUniversality_sourceTAcceptedBranch_to_phaseStateDensity
-- name    : QEC.Distillation.IdealResourceUniversality.sourceTAcceptedBranch_to_phaseStateDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:13:10.997711+00:00
-- url     : https://prove2.me/theorems/40aa4c29-6547-4396-b621-00ede9d322f1
-- title:
--   Ideal Resource Universality: source TAccepted Branch to phase State Density
-- statement:
--   The actual accepted source-T density is sent by XOR, discard, and Hadamard to
--   the exact phase-state density consumed by the subsequent injection circuit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L233-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/IdealResourceUniversality.lean#L233-L268

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

theorem QEC.Distillation.IdealResourceUniversality.sourceTAcceptedBranch_to_phaseStateDensity :
    (QuantumChannel.unitaryConj hadamardTransport).mapDensity
        ((QuantumChannel.comp TwoQubit.secondQubitDiscard
          (QuantumChannel.unitaryConj TwoQubit.xorTransport)).mapDensity
            sourceTEvenBranch) =
      phaseStateDensity (-Real.pi / 6) := by sorry
