-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_errorWordWeight_le_cube_of_hammingWeight_ge_three
-- name    : QEC.Distillation.HH18Protocol.errorWordWeight_le_cube_of_hammingWeight_ge_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:12:00.907624+00:00
-- url     : https://prove2.me/theorems/e7c35079-9e40-49a7-ba00-b7752b601eb5
-- title:
--   HH18 Protocol: error Word Weight le cube of hamming Weight ge three
-- statement:
--   The actual Bernoulli weight of any word with three or more diagonal
--   errors is at most its cubic error monomial on the declared noise interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L357-L377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L357-L377

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

theorem QEC.Distillation.HH18Protocol.errorWordWeight_le_cube_of_hammingWeight_ge_three
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord)
    (hweight : 3 ≤ HammingWeight error) :
    HH18NoisyInput.errorWordWeight epsilon error ≤ epsilon.1 ^ 3 := by sorry
