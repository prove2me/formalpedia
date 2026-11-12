-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthFreshParentNextInput_eq_noisyTInvResource
-- name    : QEC.Distillation.HH18Parameterized.routedDepthFreshParentNextInput_eq_noisyTInvResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:22:56.140206+00:00
-- url     : https://prove2.me/theorems/8dfa7090-e8bb-4ff6-b449-929047f50553
-- title:
--   HH18 Parameterized: routed Depth Fresh Parent Next Input eq noisy TInv Resource
-- statement:
--   The actual inverse-S routed input has precisely the noisy inverse-T
--   resource density at the selected port's explicit next rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L225-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L225-L238

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

theorem QEC.Distillation.HH18Parameterized.routedDepthFreshParentNextInput_eq_noisyTInvResource
    {w r m depth : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (parent : Fin (physicalInputCount m w)) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthFreshParentNextInput h hdegree state (parent, port) =
      HH18NoisyInput.noisyTInvResource
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf) := by sorry
