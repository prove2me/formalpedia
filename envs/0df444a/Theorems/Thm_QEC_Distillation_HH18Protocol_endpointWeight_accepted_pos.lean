-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_endpointWeight_accepted_pos
-- name    : QEC.Distillation.HH18Protocol.endpointWeight_accepted_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:11:52.394391+00:00
-- url     : https://prove2.me/theorems/2316dab6-11e2-4069-9837-871d93ef8b08
-- title:
--   HH18 Protocol: endpoint Weight accepted pos
-- statement:
--   The actual accepted endpoint has positive Born mass for every allowed
--   independent diagonal input distribution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L329-L333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L329-L333

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

theorem QEC.Distillation.HH18Protocol.endpointWeight_accepted_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < endpointWeight (noisyResources epsilon) .accepted := by sorry
