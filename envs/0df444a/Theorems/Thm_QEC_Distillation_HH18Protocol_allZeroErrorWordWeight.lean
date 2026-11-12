-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_allZeroErrorWordWeight
-- name    : QEC.Distillation.HH18Protocol.allZeroErrorWordWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:12:35.770989+00:00
-- url     : https://prove2.me/theorems/33510792-5218-413c-8f5c-4e1d01a21985
-- title:
--   HH18 Protocol: all Zero Error Word Weight
-- statement:
--   The all-zero physical error word has its literal product Bernoulli mass
--   over the fifteen input resources.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L279-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L279-L284

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

theorem QEC.Distillation.HH18Protocol.allZeroErrorWordWeight
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    HH18NoisyInput.errorWordWeight epsilon (0 : PhysicalErrorWord) =
      (1 - epsilon.1) ^ resourceCount := by sorry
