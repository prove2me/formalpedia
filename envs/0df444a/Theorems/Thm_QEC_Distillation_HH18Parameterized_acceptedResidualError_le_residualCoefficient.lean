-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedResidualError_le_residualCoefficient
-- name    : QEC.Distillation.HH18Parameterized.acceptedResidualError_le_residualCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:00:45.727145+00:00
-- url     : https://prove2.me/theorems/67f647d0-0a9f-4c8b-a50c-59f2e5227aae
-- title:
--   HH18 Parameterized: accepted Residual Error le residual Coefficient
-- statement:
--   The parameterized accepted residual is bounded by its explicit finite
--   coefficient times the actual code-distance error monomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L212-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L212-L239

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

theorem QEC.Distillation.HH18Parameterized.acceptedResidualError_le_residualCoefficient {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualError h hdegree epsilon ≤
      residualCoefficient w r m * epsilon.1 ^ codeDistance r w := by sorry
