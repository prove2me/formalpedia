-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:49:55.179744+00:00
-- url     : https://prove2.me/theorems/cef95d62-909e-46e4-b286-97e8b7cafedd
-- title:
--   HH18 Parameterized: routed Depth Schedule Target Error eq scale mul error Envelope
-- statement:
--   The schedule target agrees with the scaled uniform envelope, which is
--   used only as an upper-bound proof and not as the reached-error definition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L144-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L144-L151

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (depth : Nat) :
    routedDepthScheduleTargetError w r m epsilon depth =
      routedDepthIterationScale w r m *
        routedDepthErrorEnvelope w r m epsilon depth := by sorry
