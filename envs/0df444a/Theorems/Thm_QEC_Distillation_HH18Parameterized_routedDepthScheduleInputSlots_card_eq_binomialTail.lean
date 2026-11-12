-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleInputSlots_card_eq_binomialTail
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleInputSlots_card_eq_binomialTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:54:21.585188+00:00
-- url     : https://prove2.me/theorems/5f54c35b-2774-450b-9d25-bbce6cc35789
-- title:
--   HH18 Parameterized: routed Depth Schedule Input Slots card eq binomial Tail
-- statement:
--   The schedule input cardinality has the exact HH18 binomial-tail form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L311-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L311-L314

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleInputSlots_card_eq_binomialTail (m w depth : Nat) :
    Fintype.card (routedDepthScheduleInputSlots m w depth) =
      binomialTail m w ^ depth := by sorry
