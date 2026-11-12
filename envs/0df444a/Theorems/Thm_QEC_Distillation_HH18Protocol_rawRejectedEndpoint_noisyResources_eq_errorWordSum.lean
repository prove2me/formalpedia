-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_rawRejectedEndpoint_noisyResources_eq_errorWordSum
-- name    : QEC.Distillation.HH18Protocol.rawRejectedEndpoint_noisyResources_eq_errorWordSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:16:53.371148+00:00
-- url     : https://prove2.me/theorems/69d998ac-4e93-4726-9d69-a2a5d2b77d45
-- title:
--   HH18 Protocol: raw Rejected Endpoint noisy Resources eq error Word Sum
-- statement:
--   The actual noisy rejected endpoint is the finite sum of exactly the
--   rejected physical error branches under the derived independent word law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L212-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L212-L238

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instEndpointClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instEndpointClassicalDecidable

theorem QEC.Distillation.HH18Protocol.rawRejectedEndpoint_noisyResources_eq_errorWordSum
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawEndpoint (noisyResources epsilon) .rejected =
      physicalErrorWords.sum (fun error =>
        if HH18SyndromeDecoding.Accepts error then 0
        else (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
          HH18SyndromeDecoding.errorBranchOperator error) := by sorry
