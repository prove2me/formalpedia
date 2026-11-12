-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_le_scheduleTargetError
-- name    : QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_le_scheduleTargetError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:14:49.188331+00:00
-- url     : https://prove2.me/theorems/4975a375-7697-42c1-9eab-b331aeff6444
-- title:
--   HH18 Parameterized: routed Depth Error Envelope le schedule Target Error
-- statement:
--   The scale lower bound turns the envelope into a bound by the separate
--   distance-power target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L177-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L177-L184

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

theorem QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_le_scheduleTargetError {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (depth : Nat) :
    routedDepthErrorEnvelope w r m epsilon depth ≤
      routedDepthScheduleTargetError w r m epsilon depth := by sorry
