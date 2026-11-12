-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass
-- name    : QEC.Distillation.HH18Protocol.traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:26:24.909426+00:00
-- url     : https://prove2.me/theorems/3b8374fb-cdb0-4beb-8cef-bf95075c72a7
-- title:
--   HH18 Protocol: trace Norm accepted Residual Decoded Difference le two mul raw Mass
-- statement:
--   Trace norm of the decoded residual is at most twice its actual conditional
--   physical-word mass before normalization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L253-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L253-L270

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NormalizedRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u v w
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instDecodedBridgeClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instDecodedBridgeClassicalDecidable

theorem QEC.Distillation.HH18Protocol.traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    traceNorm (acceptedResidualDecodedDifference epsilon) ≤
      2 * rawAcceptedResidualErrorMass epsilon := by sorry
