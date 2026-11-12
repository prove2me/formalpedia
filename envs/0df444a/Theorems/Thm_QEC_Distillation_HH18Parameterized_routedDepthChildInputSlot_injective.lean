-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildInputSlot_injective
-- name    : QEC.Distillation.HH18Parameterized.routedDepthChildInputSlot_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:20:55.922945+00:00
-- url     : https://prove2.me/theorems/16411a27-56c5-4086-b751-0cebce88f6c9
-- title:
--   HH18 Parameterized: routed Depth Child Input Slot injective
-- statement:
--   Inputs of a fixed prefix-indexed child come from distinct parent indices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L111-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L111-L116

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

theorem QEC.Distillation.HH18Parameterized.routedDepthChildInputSlot_injective (m w depth : Nat)
    (pathPrefix : routedDepthOutputSlots m w depth) (child : LogicalSite m w) :
    Function.Injective (routedDepthChildInputSlot m w depth pathPrefix child) := by sorry
