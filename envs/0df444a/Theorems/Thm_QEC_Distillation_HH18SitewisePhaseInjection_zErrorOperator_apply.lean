-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SitewisePhaseInjection_zErrorOperator_apply
-- name    : QEC.Distillation.HH18SitewisePhaseInjection.zErrorOperator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:53:37.196137+00:00
-- url     : https://prove2.me/theorems/a0d8a874-fa10-4b36-9951-b44b522b0475
-- title:
--   HH18 Sitewise Phase Injection: z Error Operator apply
-- statement:
--   The concrete binary Pauli error acts by the corresponding support-phase product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L178-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L178-L184

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18SitewisePhaseInjection
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators

theorem QEC.Distillation.HH18SitewisePhaseInjection.zErrorOperator_apply (error : PhysicalErrorWord)
    (psi : QubitRegister PhysicalSite) (bits : Bitstring PhysicalSite) :
    HH18NoisyInput.zErrorOperator error psi bits =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport error) bits * psi bits := by sorry
