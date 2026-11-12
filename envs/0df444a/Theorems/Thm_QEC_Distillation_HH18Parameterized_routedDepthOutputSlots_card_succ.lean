-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthOutputSlots_card_succ
-- name    : QEC.Distillation.HH18Parameterized.routedDepthOutputSlots_card_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:20:50.634579+00:00
-- url     : https://prove2.me/theorems/02301b0f-7bbf-4c4f-b830-7b57e55a941f
-- title:
--   HH18 Parameterized: routed Depth Output Slots card succ
-- statement:
--   Adding one selected-port coordinate multiplies the actual routed
--   output-address count by the actual block logical-output count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L64-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L64-L68

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

theorem QEC.Distillation.HH18Parameterized.routedDepthOutputSlots_card_succ (m w depth : Nat) :
    Fintype.card (routedDepthOutputSlots m w (depth + 1)) =
      Fintype.card (routedDepthOutputSlots m w depth) * logicalOutputCount m w := by sorry
