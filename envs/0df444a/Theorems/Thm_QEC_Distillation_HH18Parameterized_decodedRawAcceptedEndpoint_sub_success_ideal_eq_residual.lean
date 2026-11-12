-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
-- name    : QEC.Distillation.HH18Parameterized.decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:04:29.525788+00:00
-- url     : https://prove2.me/theorems/efb79f72-2226-4ece-8894-a9ea5e4d20d5
-- title:
--   HH18 Parameterized: decoded Raw Accepted Endpoint sub success ideal eq residual
-- statement:
--   The decoded accepted endpoint is the error-free logical density plus its
--   centered accepted nonzero-word residual.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L202-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean#L202-L222

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

theorem QEC.Distillation.HH18Parameterized.decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    decoderChannel h (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted) -
        (acceptedBernoulliMass w r m epsilon : Complex) •
          (idealLogicalTOutput m w).toOperator =
      acceptedResidualDecodedDifference h hdegree epsilon := by sorry
