-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_rawSuccessMass_pos
-- name    : QEC.Distillation.HH18Protocol.rawSuccessMass_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:11:10.105196+00:00
-- url     : https://prove2.me/theorems/9ea415d0-7558-441a-ad29-840a67b620e7
-- title:
--   HH18 Protocol: raw Success Mass pos
-- statement:
--   The actual HH18 success probability is positive throughout the declared
--   diagonal-noise domain, so accepted normalization never relies on a surrogate
--   success assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L320-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L320-L325

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

theorem QEC.Distillation.HH18Protocol.rawSuccessMass_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < rawSuccessMass epsilon := by sorry
