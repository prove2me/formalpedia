-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleSuccessfulOutputCost_le_six_fifths
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleSuccessfulOutputCost_le_six_fifths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:14:15.944889+00:00
-- url     : https://prove2.me/theorems/bf0aad14-e42a-46f2-b240-d209faa7eaa9
-- title:
--   HH18 Parameterized: routed Depth Schedule Successful Output Cost le six fifths
-- statement:
--   The pooled expected-yield lower bound gives a uniform finite schedule
--   successful-output-cost factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L354-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L354-L361

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleSuccessfulOutputCost_le_six_fifths {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth ≤
      (6 / 5 : ℝ) * ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth := by sorry
