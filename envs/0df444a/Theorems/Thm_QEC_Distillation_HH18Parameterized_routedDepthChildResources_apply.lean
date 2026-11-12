-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildResources_apply
-- name    : QEC.Distillation.HH18Parameterized.routedDepthChildResources_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:51:19.414403+00:00
-- url     : https://prove2.me/theorems/10ef7c6e-fbf6-401c-b362-012fb806ec13
-- title:
--   HH18 Parameterized: routed Depth Child Resources apply
-- statement:
--   Every physical input of a fixed routed child has its explicit parent-port
--   provenance: the child port is fixed and only the fresh parent index varies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L257-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L257-L268

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

theorem QEC.Distillation.HH18Parameterized.routedDepthChildResources_apply {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2)
    (parent : Fin (physicalInputCount m w)) :
    routedDepthChildResources h hdegree state port hhalf parent =
      routedDepthFreshParentNextInput h hdegree state (parent, port) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.routedDepthChildResources_apply
