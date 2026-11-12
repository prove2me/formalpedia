-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawAcceptedResidualErrorMass_le_card_distance_pow
-- name    : QEC.Distillation.HH18Parameterized.rawAcceptedResidualErrorMass_le_card_distance_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:03:32.186019+00:00
-- url     : https://prove2.me/theorems/f0afe072-946b-41cd-aa08-08f4d99f00b3
-- title:
--   HH18 Parameterized: raw Accepted Residual Error Mass le card distance pow
-- statement:
--   The accepted nonzero residual mass is bounded by the actual finite number
--   of physical error words times its distance-power Bernoulli monomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L169-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L169-L188

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

theorem QEC.Distillation.HH18Parameterized.rawAcceptedResidualErrorMass_le_card_distance_pow {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawAcceptedResidualErrorMass w r m epsilon ≤
      (Fintype.card (PhysicalErrorWord m w) : ℝ) * epsilon.1 ^ codeDistance r w := by sorry
