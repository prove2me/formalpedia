-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleSuccessfulOutputCost_le_polylog
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleSuccessfulOutputCost_le_polylog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:15:42.98181+00:00
-- url     : https://prove2.me/theorems/e38993ee-3f6c-4b95-8e40-9ab7b580e6bc
-- title:
--   HH18 Parameterized: routed Depth Schedule Successful Output Cost le polylog
-- statement:
--   The literal pooled successful-output cost has the derived polylogarithmic
--   bound at every finite routed schedule depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L466-L523
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L466-L523

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleSuccessfulOutputCost_le_polylog {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth ≤
      routedDepthScheduleCostCoefficient h epsilon *
        Real.rpow
          (Real.log (1 / routedDepthScheduleTargetError w r m epsilon depth))
          (routedDepthScheduleGamma w r m) := by sorry
