-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionHistory_endpoint
-- name    : QEC.Distillation.PhaseInjection.phaseInjectionHistory_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:23:51.69327+00:00
-- url     : https://prove2.me/theorems/d39bc9c8-a010-4d01-b16b-0136dfa3a9d0
-- title:
--   Phase Injection: phase Injection History endpoint
-- statement:
--   The cyclic retry endpoint is exactly the history exponent modulo the cycle order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L999-L1007
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L999-L1007

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct

theorem QEC.Distillation.PhaseInjection.phaseInjectionHistory_endpoint (q : Nat) (start : ZMod q) (coins : List Bool) :
    PhaseRetry.endpoint start coins =
      start + (phaseInjectionHistoryExponent coins : ZMod q) := by sorry
