-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleLogGrowthBase_pos
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleLogGrowthBase_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:50:25.274639+00:00
-- url     : https://prove2.me/theorems/12a9ab3c-7549-4aef-a7c4-25e830a2a130
-- title:
--   HH18 Parameterized: routed Depth Schedule Log Growth Base pos
-- statement:
--   Initial smallness supplies a positive logarithmic growth base.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L426-L434
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L426-L434

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleLogGrowthBase_pos {w r m : Nat}
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    0 < routedDepthScheduleLogGrowthBase w r m epsilon := by sorry
