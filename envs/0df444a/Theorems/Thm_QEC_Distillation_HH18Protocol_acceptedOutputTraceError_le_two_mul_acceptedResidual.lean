-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_acceptedOutputTraceError_le_two_mul_acceptedResidual
-- name    : QEC.Distillation.HH18Protocol.acceptedOutputTraceError_le_two_mul_acceptedResidual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:28:02.346011+00:00
-- url     : https://prove2.me/theorems/65e3ec7f-7307-4f47-b7b3-64441b71f841
-- title:
--   HH18 Protocol: accepted Output Trace Error le two mul accepted Residual
-- statement:
--   Honest bridge from the decoded accepted output's actual trace-norm error
--   to the physically proved accepted nonzero-word residual.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L296-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean#L296-L328

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

theorem QEC.Distillation.HH18Protocol.acceptedOutputTraceError_le_two_mul_acceptedResidual
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18OutputTraceError
      (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
      idealLogicalTOutput ≤ 2 * acceptedResidualError epsilon := by sorry
