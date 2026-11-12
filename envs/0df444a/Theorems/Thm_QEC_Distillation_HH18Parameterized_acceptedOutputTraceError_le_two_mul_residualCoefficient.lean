-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedOutputTraceError_le_two_mul_residualCoefficient
-- name    : QEC.Distillation.HH18Parameterized.acceptedOutputTraceError_le_two_mul_residualCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:11:08.109767+00:00
-- url     : https://prove2.me/theorems/e25fa03e-88bb-4c27-91c0-cd588d0e736a
-- title:
--   HH18 Parameterized: accepted Output Trace Error le two mul residual Coefficient
-- statement:
--   The decoded trace error has the explicit finite-coefficient distance-power
--   bound inherited from the accepted residual.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L266-L281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L266-L281

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

theorem QEC.Distillation.HH18Parameterized.acceptedOutputTraceError_le_two_mul_residualCoefficient {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    outputTraceError
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
      (idealLogicalTOutput m w) ≤
        2 * residualCoefficient w r m * epsilon.1 ^ codeDistance r w := by sorry
