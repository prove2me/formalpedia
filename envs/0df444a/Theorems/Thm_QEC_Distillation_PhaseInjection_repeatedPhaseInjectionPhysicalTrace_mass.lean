-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionPhysicalTrace_mass
-- name    : QEC.Distillation.PhaseInjection.repeatedPhaseInjectionPhysicalTrace_mass
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:23:12.463458+00:00
-- url     : https://prove2.me/theorems/1af2e9e5-c645-4f19-a30a-a8b79936fa99
-- title:
--   Phase Injection: repeated Phase Injection Physical Trace mass
-- statement:
--   The physical trace mass is the product of the actual instrument Born weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1248-L1261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1248-L1261

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

theorem QEC.Distillation.PhaseInjection.repeatedPhaseInjectionPhysicalTrace_mass (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionPhysicalTrace theta coins psi hpsi).2.2 =
      repeatedPhaseInjectionHistoryWeight theta coins psi hpsi := by sorry
