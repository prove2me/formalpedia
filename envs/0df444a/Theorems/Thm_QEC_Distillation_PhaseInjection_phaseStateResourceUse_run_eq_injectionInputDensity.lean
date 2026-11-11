-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseStateResourceUse_run_eq_injectionInputDensity
-- name    : QEC.Distillation.PhaseInjection.phaseStateResourceUse_run_eq_injectionInputDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:21:25.420753+00:00
-- url     : https://prove2.me/theorems/0128da2a-9d38-4573-bb38-aaf52ca796d4
-- title:
--   Phase Injection: phase State Resource Use run eq injection Input Density
-- statement:
--   Executing the resource-use term gives exactly the density of the literal circuit input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L678-L694
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L678-L694

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

theorem QEC.Distillation.PhaseInjection.phaseStateResourceUse_run_eq_injectionInputDensity
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    (phaseStateResourceUse theta).run (sourceInputDensity psi hpsi) =
      injectionInputDensity psi theta hpsi := by sorry
