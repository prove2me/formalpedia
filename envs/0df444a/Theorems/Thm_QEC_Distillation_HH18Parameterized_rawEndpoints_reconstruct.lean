-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawEndpoints_reconstruct
-- name    : QEC.Distillation.HH18Parameterized.rawEndpoints_reconstruct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:29:53.895689+00:00
-- url     : https://prove2.me/theorems/83f0d480-960d-421b-b404-43f811ffca96
-- title:
--   HH18 Parameterized: raw Endpoints reconstruct
-- statement:
--   The two literal raw endpoints reconstruct the complete composed physical
--   operation on the actual measured resource record.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PhysicalEndpoint.lean#L96-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PhysicalEndpoint.lean#L96-L108

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

theorem QEC.Distillation.HH18Parameterized.rawEndpoints_reconstruct {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    rawEndpoint h hdegree inputs .accepted + rawEndpoint h hdegree inputs .rejected =
      ((physicalOperation h hdegree).mapDensity
        (prepareMeasuredResources m w inputs)).toOperator := by sorry
