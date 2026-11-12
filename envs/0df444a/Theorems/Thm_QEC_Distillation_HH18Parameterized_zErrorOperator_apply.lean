-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_zErrorOperator_apply
-- name    : QEC.Distillation.HH18Parameterized.zErrorOperator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:56:25.7202+00:00
-- url     : https://prove2.me/theorems/e0de93aa-c7f2-4c55-b14c-b5b4d55831bd
-- title:
--   HH18 Parameterized: z Error Operator apply
-- statement:
--   The concrete binary Pauli error acts by the corresponding support-phase product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L176-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L176-L182

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.zErrorOperator_apply {m w : Nat} (error : PhysicalErrorWord m w)
    (psi : PhysicalRegister m w) (bits : Bitstring (PhysicalSite m w)) :
    HH18NoisyInput.zErrorOperator error psi bits =
      Qubit.zSupportPhase (PauliSymplectic.binarySupport error) bits * psi bits := by sorry
