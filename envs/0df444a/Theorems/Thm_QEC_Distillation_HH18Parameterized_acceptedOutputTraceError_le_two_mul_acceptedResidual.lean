-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedOutputTraceError_le_two_mul_acceptedResidual
-- name    : QEC.Distillation.HH18Parameterized.acceptedOutputTraceError_le_two_mul_acceptedResidual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:37:38.450198+00:00
-- url     : https://prove2.me/theorems/833a242c-ff0f-4ebb-b7fa-25aa986f7bdf
-- title:
--   HH18 Parameterized: accepted Output Trace Error le two mul accepted Residual
-- statement:
--   The actual positive accepted decoded output has trace error controlled by
--   twice the actual normalized accepted residual.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L226-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L226-L262

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

theorem QEC.Distillation.HH18Parameterized.acceptedOutputTraceError_le_two_mul_acceptedResidual {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    outputTraceError
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
      (idealLogicalTOutput m w) ≤ 2 * acceptedResidualError h hdegree epsilon := by sorry
