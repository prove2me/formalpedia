-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleSuccessfulOutputCost_eq
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleSuccessfulOutputCost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:54:27.826714+00:00
-- url     : https://prove2.me/theorems/f0f93088-eb49-4499-9d16-8083b65c4f08
-- title:
--   HH18 Parameterized: routed Depth Schedule Successful Output Cost eq
-- statement:
--   The schedule successful-output cost uses the pooled expected yield and
--   the actual finite routed input/output ratio.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L333-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L333-L341

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleSuccessfulOutputCost_eq {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth =
      ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth /
        (routedDepthScheduleExpectedYield h hdegree epsilon hsmall depth : ℝ) := by sorry
