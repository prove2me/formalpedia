-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionPhysicalTrace_ledger
-- name    : QEC.Distillation.PhaseInjection.repeatedPhaseInjectionPhysicalTrace_ledger
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:23:22.197829+00:00
-- url     : https://prove2.me/theorems/5d402d73-ad1c-4f87-9354-a446dfed560d
-- title:
--   Phase Injection: repeated Phase Injection Physical Trace ledger
-- statement:
--   The physical trace ledger is the resource ledger of the same retry execution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1232-L1245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1232-L1245

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

theorem QEC.Distillation.PhaseInjection.repeatedPhaseInjectionPhysicalTrace_ledger (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionPhysicalTrace theta coins psi hpsi).2.1 =
      repeatedPhaseInjectionLedger theta coins psi hpsi := by sorry
