-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleExpectedYield_five_sixths_le
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleExpectedYield_five_sixths_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:52:35.839869+00:00
-- url     : https://prove2.me/theorems/e0785682-cd2d-41cf-bc7f-4572e5e24774
-- title:
--   HH18 Parameterized: routed Depth Schedule Expected Yield five sixths le
-- statement:
--   The actual schedule expected yield has the uniform positive lower bound
--   already proved from literal finite path products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L281-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L281-L287

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleExpectedYield_five_sixths_le {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (5 / 6 : ℝ) ≤ (routedDepthScheduleExpectedYield h hdegree epsilon hsmall depth : ℝ) := by sorry
