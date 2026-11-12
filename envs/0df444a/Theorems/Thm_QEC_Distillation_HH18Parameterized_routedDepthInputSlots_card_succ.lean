-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthInputSlots_card_succ
-- name    : QEC.Distillation.HH18Parameterized.routedDepthInputSlots_card_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:18:37.473519+00:00
-- url     : https://prove2.me/theorems/baf80581-2684-4b09-8f0b-b03734925cba
-- title:
--   HH18 Parameterized: routed Depth Input Slots card succ
-- statement:
--   Adding one physical resource coordinate multiplies the actual routed
--   input-address count by the actual block input count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L56-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L56-L60

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

theorem QEC.Distillation.HH18Parameterized.routedDepthInputSlots_card_succ (m w depth : Nat) :
    Fintype.card (routedDepthInputSlots m w (depth + 1)) =
      Fintype.card (routedDepthInputSlots m w depth) * physicalInputCount m w := by sorry
