-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthFreshParentDephasedOutput_eq_depthTwoFreshParentDephasedOutput
-- name    : QEC.Distillation.HH18Parameterized.routedDepthFreshParentDephasedOutput_eq_depthTwoFreshParentDephasedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:22:49.768202+00:00
-- url     : https://prove2.me/theorems/153a47e9-2f78-40f9-b3f2-5572551f27d8
-- title:
--   HH18 Parameterized: routed Depth Fresh Parent Dephased Output eq depth Two Fresh Parent Dephased Output
-- statement:
--   The indexed-pool dephased output is exactly the existing actual
--   depth-two parent-output dephasing at the routed state rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L200-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L200-L209

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

theorem QEC.Distillation.HH18Parameterized.routedDepthFreshParentDephasedOutput_eq_depthTwoFreshParentDephasedOutput
    {w r m depth : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (source : depthTwoParentOutputSlots m w) :
    routedDepthFreshParentDephasedOutput h hdegree state source =
      depthTwoFreshParentDephasedOutput h hdegree rate source := by sorry
