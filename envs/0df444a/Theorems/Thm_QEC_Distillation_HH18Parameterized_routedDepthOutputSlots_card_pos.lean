-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthOutputSlots_card_pos
-- name    : QEC.Distillation.HH18Parameterized.routedDepthOutputSlots_card_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:40:48.094192+00:00
-- url     : https://prove2.me/theorems/cfeccc5c-0bef-455b-b433-b40eed23b1f9
-- title:
--   HH18 Parameterized: routed Depth Output Slots card pos
-- statement:
--   The finite routed output-slot carrier therefore has positive cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L289-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L289-L291

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
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

theorem QEC.Distillation.HH18Parameterized.routedDepthOutputSlots_card_pos (m w depth : Nat) :
    0 < Fintype.card (routedDepthOutputSlots m w depth) := by sorry
