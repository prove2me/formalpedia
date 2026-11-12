-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_acceptedResidualError_le_cubic
-- name    : QEC.Distillation.HH18Protocol.acceptedResidualError_le_cubic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:12:05.350844+00:00
-- url     : https://prove2.me/theorems/8555fe03-3f9b-468e-8f97-f76c2f56f149
-- title:
--   HH18 Protocol: accepted Residual Error le cubic
-- statement:
--   The HH18 distance-three route gives a genuine cubic accepted-error bound
--   from the physical Bernoulli histories: for fixed `n = 15`, this is
--   `O((n * epsilon)^3)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L436-L458
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L436-L458

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

theorem QEC.Distillation.HH18Protocol.acceptedResidualError_le_cubic
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualError epsilon ≤ residualCubicCoefficient * epsilon.1 ^ 3 := by sorry
