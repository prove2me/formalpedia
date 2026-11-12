-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildRun_success_pos
-- name    : QEC.Distillation.HH18Parameterized.routedDepthChildRun_success_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:22:51.719365+00:00
-- url     : https://prove2.me/theorems/02206054-6882-4296-8556-d5e904b2d30e
-- title:
--   HH18 Parameterized: routed Depth Child Run success pos
-- statement:
--   The accepted Born mass of every explicitly constructed routed child run
--   is positive at its domain-certified successor rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L330-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L330-L341

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
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

theorem QEC.Distillation.HH18Parameterized.routedDepthChildRun_success_pos {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    0 < (routedDepthChildRun h hdegree state port hhalf).successProbability := by sorry
