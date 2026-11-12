-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_physicalErrorWord_card
-- name    : QEC.Distillation.HH18Protocol.physicalErrorWord_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:17:32.067099+00:00
-- url     : https://prove2.me/theorems/95cd0b31-b0a0-43a3-8841-acc83443c315
-- title:
--   HH18 Protocol: physical Error Word card
-- statement:
--   The real finite error-history type has exactly the binary words over the
--   fifteen physical resource sites.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L381-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhysicalEndpoint.lean#L381-L382

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

theorem QEC.Distillation.HH18Protocol.physicalErrorWord_card : Fintype.card PhysicalErrorWord = 2 ^ resourceCount := by sorry
