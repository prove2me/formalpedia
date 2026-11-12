-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildResources_eq_depthTwoChildResources
-- name    : QEC.Distillation.HH18Parameterized.routedDepthChildResources_eq_depthTwoChildResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:11:01.630709+00:00
-- url     : https://prove2.me/theorems/2a9c97da-899a-4071-a890-2f39f89724d8
-- title:
--   HH18 Parameterized: routed Depth Child Resources eq depth Two Child Resources
-- statement:
--   The routed finite-depth child resources agree definitionally with the
--   already-proved actual depth-two construction at the state rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L272-L282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L272-L282

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

theorem QEC.Distillation.HH18Parameterized.routedDepthChildResources_eq_depthTwoChildResources {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthChildResources h hdegree state port hhalf =
      depthTwoChildResources h hdegree rate port hhalf := by sorry
