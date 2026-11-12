-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthSchedule_rpow_distancePow_eq_inputOutputRatio_pow
-- name    : QEC.Distillation.HH18Parameterized.routedDepthSchedule_rpow_distancePow_eq_inputOutputRatio_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:51:12.110174+00:00
-- url     : https://prove2.me/theorems/aa37aebb-ff8f-426a-b684-61ab25793ba0
-- title:
--   HH18 Parameterized: routed Depth Schedule rpow distance Pow eq input Output Ratio pow
-- statement:
--   The real-power form of the schedule exponent exactly recovers the actual
--   finite routed input/output ratio at every depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L385-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L385-L423

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

theorem QEC.Distillation.HH18Parameterized.routedDepthSchedule_rpow_distancePow_eq_inputOutputRatio_pow
    {w r m : Nat} (h : Admissible w r m) (depth : Nat) :
    Real.rpow ((codeDistance r w : ℝ) ^ depth)
        (routedDepthScheduleGamma w r m) =
      ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth := by sorry
