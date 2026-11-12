-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_rawSuccessMass_allZeroWord_le
-- name    : QEC.Distillation.HH18Protocol.rawSuccessMass_allZeroWord_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:11:13.76122+00:00
-- url     : https://prove2.me/theorems/2dd49cf1-efab-4eea-8b75-8fc1b27b5f87
-- title:
--   HH18 Protocol: raw Success Mass all Zero Word le
-- statement:
--   The actual accepted mass contains the nonnegative all-zero physical
--   summand; this is a local one-block statement and makes no simultaneous-batch
--   success assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L289-L315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L289-L315

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

theorem QEC.Distillation.HH18Protocol.rawSuccessMass_allZeroWord_le
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (1 - epsilon.1) ^ resourceCount ≤ rawSuccessMass epsilon := by sorry
