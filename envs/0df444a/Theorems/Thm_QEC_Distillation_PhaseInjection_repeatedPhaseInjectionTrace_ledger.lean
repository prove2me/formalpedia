-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionTrace_ledger
-- name    : QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_ledger
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:38:07.465739+00:00
-- url     : https://prove2.me/theorems/7ab3d2a1-eead-4bbd-a534-e9db2d79ea04
-- title:
--   Phase Injection: repeated Phase Injection Trace ledger
-- statement:
--   The ledger projection is definitionally the resource component of the concrete trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L941-L945
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L941-L945

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

theorem QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_ledger (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionTrace theta coins psi hpsi).2 =
      repeatedPhaseInjectionLedger theta coins psi hpsi := by sorry
