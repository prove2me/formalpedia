-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_endpointWeight_accepted_eq_rawSuccessMass
-- name    : QEC.Distillation.HH18Protocol.endpointWeight_accepted_eq_rawSuccessMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:11:10.463376+00:00
-- url     : https://prove2.me/theorems/748832b6-2140-4be5-bf37-78a3e65b8489
-- title:
--   HH18 Protocol: endpoint Weight accepted eq raw Success Mass
-- statement:
--   The accepted Born weight is exactly the accepted sum under the derived
--   independent physical error law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L250-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L250-L275

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

theorem QEC.Distillation.HH18Protocol.endpointWeight_accepted_eq_rawSuccessMass
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    endpointWeight (noisyResources epsilon) .accepted = rawSuccessMass epsilon := by sorry
