-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedResidualError_le_sourceScaled
-- name    : QEC.Distillation.HH18Parameterized.acceptedResidualError_le_sourceScaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:01:03.863708+00:00
-- url     : https://prove2.me/theorems/a18d73d0-5075-42dc-97ee-5c5d1073f685
-- title:
--   HH18 Parameterized: accepted Residual Error le source Scaled
-- statement:
--   A source-facing form of the finite residual theorem in the conventional
--   `(n * ε)^d` scale, where `n` is the actual physical input count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L253-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L253-L270

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

theorem QEC.Distillation.HH18Parameterized.acceptedResidualError_le_sourceScaled {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualError h hdegree epsilon ≤
      residualCoefficient w r m *
        ((physicalInputCount m w : ℝ) * epsilon.1) ^ codeDistance r w := by sorry
