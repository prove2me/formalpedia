-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawAcceptedEndpoint_noisyResources_eq_errorWordSum
-- name    : QEC.Distillation.HH18Parameterized.rawAcceptedEndpoint_noisyResources_eq_errorWordSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:58:13.927515+00:00
-- url     : https://prove2.me/theorems/776d7eda-b227-4fa0-afce-bdb17cf25d8e
-- title:
--   HH18 Parameterized: raw Accepted Endpoint noisy Resources eq error Word Sum
-- statement:
--   The actual noisy accepted endpoint is the finite sum of exactly the
--   accepted physical error branches under the derived independent word law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PhysicalEndpoint.lean#L180-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PhysicalEndpoint.lean#L180-L207

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_EndpointSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
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
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instEndpointClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instEndpointClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.rawAcceptedEndpoint_noisyResources_eq_errorWordSum {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawEndpoint h hdegree (noisyResources m w epsilon) .accepted =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            errorBranchOperator h hdegree error
        else 0) := by sorry
