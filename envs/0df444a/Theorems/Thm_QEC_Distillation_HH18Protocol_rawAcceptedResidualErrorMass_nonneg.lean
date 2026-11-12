-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_rawAcceptedResidualErrorMass_nonneg
-- name    : QEC.Distillation.HH18Protocol.rawAcceptedResidualErrorMass_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:12:14.988669+00:00
-- url     : https://prove2.me/theorems/ed204105-5f16-4609-b750-7a7d2a21eaca
-- title:
--   HH18 Protocol: raw Accepted Residual Error Mass nonneg
-- statement:
--   The HH18 Protocol construction uses the raw Accepted Residual Error Mass nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L345-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L345-L353

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

theorem QEC.Distillation.HH18Protocol.rawAcceptedResidualErrorMass_nonneg
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 ≤ rawAcceptedResidualErrorMass epsilon := by sorry
