-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleOutputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleOutputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:14:18.749201+00:00
-- url     : https://prove2.me/theorems/063a0867-1e9f-4a03-a30e-b430bbbf5430
-- title:
--   HH18 Parameterized: routed Depth Schedule Output Slots card
-- statement:
--   The actual finite logical schedule carrier has exact `k^z` size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L305-L308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L305-L308

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleOutputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthScheduleOutputSlots m w depth) =
      logicalOutputCount m w ^ depth := by sorry
