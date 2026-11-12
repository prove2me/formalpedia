-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildInputSlot_apply
-- name    : QEC.Distillation.HH18Parameterized.routedDepthChildInputSlot_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:51:33.889996+00:00
-- url     : https://prove2.me/theorems/e30cc86d-b76f-4b48-a63c-b3baa37f843c
-- title:
--   HH18 Parameterized: routed Depth Child Input Slot apply
-- statement:
--   The HH18 Parameterized construction uses the routed Depth Child Input Slot apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L103-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L103-L108

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.routedDepthChildInputSlot_apply (m w depth : Nat)
    (pathPrefix : routedDepthOutputSlots m w depth) (child : LogicalSite m w)
    (parent : Fin (physicalInputCount m w)) :
    routedDepthChildInputSlot m w depth pathPrefix child parent =
      (pathPrefix, (child, parent)) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.routedDepthChildInputSlot_apply
