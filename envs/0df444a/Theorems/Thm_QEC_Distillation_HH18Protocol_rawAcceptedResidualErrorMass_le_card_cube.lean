-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_rawAcceptedResidualErrorMass_le_card_cube
-- name    : QEC.Distillation.HH18Protocol.rawAcceptedResidualErrorMass_le_card_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:13:53.635841+00:00
-- url     : https://prove2.me/theorems/0414698d-c6da-4c40-9246-5cf30a4b4ab0
-- title:
--   HH18 Protocol: raw Accepted Residual Error Mass le card cube
-- statement:
--   The residual accepted error mass is bounded using only the actual HH18
--   acceptance predicate.  Each surviving nonzero word has Hamming weight at
--   least three by the code's proved distance route.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L387-L408
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L387-L408

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

theorem QEC.Distillation.HH18Protocol.rawAcceptedResidualErrorMass_le_card_cube
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawAcceptedResidualErrorMass epsilon ≤
      (Fintype.card PhysicalErrorWord : ℝ) * epsilon.1 ^ 3 := by sorry
