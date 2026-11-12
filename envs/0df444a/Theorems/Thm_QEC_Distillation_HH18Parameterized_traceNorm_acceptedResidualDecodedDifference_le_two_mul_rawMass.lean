-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass
-- name    : QEC.Distillation.HH18Parameterized.traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:04:55.983046+00:00
-- url     : https://prove2.me/theorems/d461a529-8b7b-48c7-83ac-b1e55274d2de
-- title:
--   HH18 Parameterized: trace Norm accepted Residual Decoded Difference le two mul raw Mass
-- statement:
--   The decoded residual has trace norm at most twice its actual unnormalized
--   accepted nonzero-word mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L180-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L180-L198

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
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
universe u v w
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    traceNorm (acceptedResidualDecodedDifference h hdegree epsilon) ≤
      2 * rawAcceptedResidualErrorMass w r m epsilon := by sorry
