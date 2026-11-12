-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildRun_eq_resourceDecodedRun
-- name    : QEC.Distillation.HH18Parameterized.routedDepthChildRun_eq_resourceDecodedRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:51:46.311193+00:00
-- url     : https://prove2.me/theorems/7a6a4c59-27ac-4fa5-acd1-ce61310ef5b9
-- title:
--   HH18 Parameterized: routed Depth Child Run eq resource Decoded Run
-- statement:
--   The child run of a routed state is the ordinary actual one-level run at
--   the selected port's exact next physical rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L314-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L314-L326

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

theorem QEC.Distillation.HH18Parameterized.routedDepthChildRun_eq_resourceDecodedRun {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthChildRun h hdegree state port hhalf =
      resourceDecodedRun h hdegree (noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf)) := by sorry
