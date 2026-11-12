-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleInputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleInputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:13:40.411782+00:00
-- url     : https://prove2.me/theorems/f563995a-26c2-4141-ac0a-259df60bdcf9
-- title:
--   HH18 Parameterized: routed Depth Schedule Input Slots card
-- statement:
--   The actual finite physical schedule carrier has exact `n^z` size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L299-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L299-L302

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleInputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthScheduleInputSlots m w depth) =
      physicalInputCount m w ^ depth := by sorry
