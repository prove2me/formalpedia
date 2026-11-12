-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_physicalErrorWord_card
-- name    : QEC.Distillation.HH18Parameterized.physicalErrorWord_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:03:20.335006+00:00
-- url     : https://prove2.me/theorems/b0745555-5456-40a0-8e9d-52bcec5f7098
-- title:
--   HH18 Parameterized: physical Error Word card
-- statement:
--   The actual physical error-history type has exactly the binary-word
--   cardinality of the parameterized physical input carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L163-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L163-L165

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.physicalErrorWord_card (m w : Nat) :
    Fintype.card (PhysicalErrorWord m w) = 2 ^ physicalInputCount m w := by sorry
