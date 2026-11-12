-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleTargetError_exists_lt
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleTargetError_exists_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:52:37.048192+00:00
-- url     : https://prove2.me/theorems/3693a232-1943-4c32-918a-38c92f396b85
-- title:
--   HH18 Parameterized: routed Depth Schedule Target Error exists lt
-- statement:
--   The fixed-base distance-power target falls below every positive threshold
--   at some finite routed schedule depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L239-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L239-L268

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleTargetError_exists_lt {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (target : ℝ) (htarget : 0 < target) :
    ∃ depth : Nat, routedDepthScheduleTargetError w r m epsilon depth < target := by sorry
