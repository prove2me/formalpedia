-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedOutputTraceError_le_two_mul_sourceScaled
-- name    : QEC.Distillation.HH18Parameterized.acceptedOutputTraceError_le_two_mul_sourceScaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:13:57.798581+00:00
-- url     : https://prove2.me/theorems/cf37675c-2b6b-4fc7-81c7-cc9711cec8ec
-- title:
--   HH18 Parameterized: accepted Output Trace Error le two mul source Scaled
-- statement:
--   The decoded trace error has the source-facing `(n * epsilon)^d` bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L284-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L284-L302

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

theorem QEC.Distillation.HH18Parameterized.acceptedOutputTraceError_le_two_mul_sourceScaled {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    outputTraceError
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
      (idealLogicalTOutput m w) ≤
        2 * residualCoefficient w r m *
          ((physicalInputCount m w : ℝ) * epsilon.1) ^ codeDistance r w := by sorry
