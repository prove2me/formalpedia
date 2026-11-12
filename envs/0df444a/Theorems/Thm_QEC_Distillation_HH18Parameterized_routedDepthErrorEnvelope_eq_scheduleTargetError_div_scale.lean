-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_eq_scheduleTargetError_div_scale
-- name    : QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_eq_scheduleTargetError_div_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:52:48.614884+00:00
-- url     : https://prove2.me/theorems/f82ee9e5-78c4-4d03-8baa-5bcea1054ff5
-- title:
--   HH18 Parameterized: routed Depth Error Envelope eq schedule Target Error div scale
-- statement:
--   The uniform envelope is exactly the distance-power target divided by the
--   positive routing scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L155-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L155-L162

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

theorem QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_eq_scheduleTargetError_div_scale {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (depth : Nat) :
    routedDepthErrorEnvelope w r m epsilon depth =
      routedDepthScheduleTargetError w r m epsilon depth /
        routedDepthIterationScale w r m := by sorry
