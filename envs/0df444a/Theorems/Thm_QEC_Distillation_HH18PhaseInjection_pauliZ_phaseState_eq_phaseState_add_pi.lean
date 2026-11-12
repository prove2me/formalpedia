-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PhaseInjection_pauliZ_phaseState_eq_phaseState_add_pi
-- name    : QEC.Distillation.HH18PhaseInjection.pauliZ_phaseState_eq_phaseState_add_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:33:57.470851+00:00
-- url     : https://prove2.me/theorems/836bd8aa-1035-47a5-ba9d-f8f0bf381d02
-- title:
--   HH18 Phase Injection: pauli Z phase State eq phase State add pi
-- statement:
--   A physical Pauli-`Z` error on a phase state is exactly a `pi` angle shift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L54-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L54-L66

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit

theorem QEC.Distillation.HH18PhaseInjection.pauliZ_phaseState_eq_phaseState_add_pi (theta : Real) :
    pauliZ (OneQubitMagic.phaseState theta) =
      OneQubitMagic.phaseState (theta + Real.pi) := by sorry
