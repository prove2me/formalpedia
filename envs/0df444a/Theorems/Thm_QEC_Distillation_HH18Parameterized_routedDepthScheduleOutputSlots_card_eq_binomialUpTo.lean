-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleOutputSlots_card_eq_binomialUpTo
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleOutputSlots_card_eq_binomialUpTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:54:41.007989+00:00
-- url     : https://prove2.me/theorems/01ee2402-3d7c-46c8-bd1f-8377ea142339
-- title:
--   HH18 Parameterized: routed Depth Schedule Output Slots card eq binomial Up To
-- statement:
--   The schedule output cardinality has the exact HH18 cumulative-binomial
--   form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L318-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L318-L321

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleOutputSlots_card_eq_binomialUpTo (m w depth : Nat) :
    Fintype.card (routedDepthScheduleOutputSlots m w depth) =
      binomialUpTo m w ^ depth := by sorry
