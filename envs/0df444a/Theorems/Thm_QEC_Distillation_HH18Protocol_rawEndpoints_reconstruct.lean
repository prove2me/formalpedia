-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_rawEndpoints_reconstruct
-- name    : QEC.Distillation.HH18Protocol.rawEndpoints_reconstruct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:16:03.972655+00:00
-- url     : https://prove2.me/theorems/b1bddc0c-d6f5-4f5e-ac23-582d9b894255
-- title:
--   HH18 Protocol: raw Endpoints reconstruct
-- statement:
--   The HH18 Protocol construction uses the raw Endpoints reconstruct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L61-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L61-L73

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

theorem QEC.Distillation.HH18Protocol.rawEndpoints_reconstruct
    (inputs : ResourceInput resourceCount QubitSpace) :
    rawEndpoint inputs .accepted + rawEndpoint inputs .rejected =
      (physicalOperation.mapDensity (prepareMeasuredResources inputs)).toOperator := by sorry
