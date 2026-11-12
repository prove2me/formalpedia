-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_endpointWeights_sum
-- name    : QEC.Distillation.HH18Protocol.endpointWeights_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:12:22.610487+00:00
-- url     : https://prove2.me/theorems/3750264c-8cec-4b18-a608-f1d92db4a5d1
-- title:
--   HH18 Protocol: endpoint Weights sum
-- statement:
--   The HH18 Protocol construction uses the endpoint Weights sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L56-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L56-L59

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

theorem QEC.Distillation.HH18Protocol.endpointWeights_sum
    (inputs : ResourceInput resourceCount QubitSpace) :
    endpointWeight inputs .accepted + endpointWeight inputs .rejected = 1 := by sorry
