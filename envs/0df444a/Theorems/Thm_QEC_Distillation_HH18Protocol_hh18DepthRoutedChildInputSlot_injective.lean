-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthRoutedChildInputSlot_injective
-- name    : QEC.Distillation.HH18Protocol.hh18DepthRoutedChildInputSlot_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:30:23.492444+00:00
-- url     : https://prove2.me/theorems/712ca443-985f-4e35-b545-9ae813c70bca
-- title:
--   HH18 Protocol: hh18 Depth Routed Child Input Slot injective
-- statement:
--   Routing is injective within the fixed child, so its fifteen inputs use
--   distinct indexed parent executions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L807-L813
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L807-L813

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

theorem QEC.Distillation.HH18Protocol.hh18DepthRoutedChildInputSlot_injective (depth : Nat)
    (port : BatchOutputPort) :
    Function.Injective (hh18DepthRoutedChildInputSlot depth port) := by sorry
