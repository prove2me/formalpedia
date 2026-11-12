-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthOutputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.routedDepthOutputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:51:48.499753+00:00
-- url     : https://prove2.me/theorems/38b243c7-8ea7-4598-bcfa-51adcf853f6c
-- title:
--   HH18 Parameterized: routed Depth Output Slots card
-- statement:
--   The exact cardinality of the finite routed logical-output address carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L49-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L49-L52

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

theorem QEC.Distillation.HH18Parameterized.routedDepthOutputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthOutputSlots m w depth) =
      logicalOutputCount m w ^ depth := by sorry
