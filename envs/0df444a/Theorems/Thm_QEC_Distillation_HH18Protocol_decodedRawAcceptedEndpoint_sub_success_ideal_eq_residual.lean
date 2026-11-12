-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
-- name    : QEC.Distillation.HH18Protocol.decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:28:25.690245+00:00
-- url     : https://prove2.me/theorems/a9b1a0b1-1adc-486b-b40b-f6b5af379c6d
-- title:
--   HH18 Protocol: decoded Raw Accepted Endpoint sub success ideal eq residual
-- statement:
--   The actual decoded accepted endpoint is the error-free logical density
--   plus precisely the centered accepted nonzero-word residual.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L274-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L274-L292

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

theorem QEC.Distillation.HH18Protocol.decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    decoderChannel (rawEndpoint (noisyResources epsilon) .accepted) -
        (rawSuccessMass epsilon : Complex) • idealLogicalTOutput.toOperator =
      acceptedResidualDecodedDifference epsilon := by sorry
