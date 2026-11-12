-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleSuccessfulOutputCost_pos
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleSuccessfulOutputCost_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:54:39.169958+00:00
-- url     : https://prove2.me/theorems/a736f35d-7b04-434d-af28-511bd1d9f4c5
-- title:
--   HH18 Parameterized: routed Depth Schedule Successful Output Cost pos
-- statement:
--   The actual finite schedule successful-output cost remains positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L344-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L344-L350

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleSuccessfulOutputCost_pos {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    0 < routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth := by sorry
