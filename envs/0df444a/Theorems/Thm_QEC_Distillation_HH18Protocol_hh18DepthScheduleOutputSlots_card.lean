-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleOutputSlots_card
-- name    : QEC.Distillation.HH18Protocol.hh18DepthScheduleOutputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:32:57.458115+00:00
-- url     : https://prove2.me/theorems/516a6a92-e4d5-458e-a616-444ddea7fc87
-- title:
--   HH18 Protocol: hh18 Depth Schedule Output Slots card
-- statement:
--   The actual finite output-slot count is exactly one to the schedule
--   depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1251-L1253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1251-L1253

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
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
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic

theorem QEC.Distillation.HH18Protocol.hh18DepthScheduleOutputSlots_card (depth : Nat) :
    Fintype.card (hh18DepthScheduleOutputSlots depth) = 1 ^ depth := by sorry
