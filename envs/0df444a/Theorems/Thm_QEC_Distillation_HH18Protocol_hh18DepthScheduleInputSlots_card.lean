-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleInputSlots_card
-- name    : QEC.Distillation.HH18Protocol.hh18DepthScheduleInputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:32:33.550088+00:00
-- url     : https://prove2.me/theorems/d0e68638-38ca-4304-bc67-d4bf42513759
-- title:
--   HH18 Protocol: hh18 Depth Schedule Input Slots card
-- statement:
--   The actual finite input-slot count is exactly fifteen to the schedule
--   depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1245-L1247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L1245-L1247

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

theorem QEC.Distillation.HH18Protocol.hh18DepthScheduleInputSlots_card (depth : Nat) :
    Fintype.card (hh18DepthScheduleInputSlots depth) = 15 ^ depth := by sorry
