-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildResources_eq_noisyResources
-- name    : QEC.Distillation.HH18Parameterized.routedDepthChildResources_eq_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:09:27.883127+00:00
-- url     : https://prove2.me/theorems/bb6d999b-3147-4077-bbe4-dee413274461
-- title:
--   HH18 Parameterized: routed Depth Child Resources eq noisy Resources
-- statement:
--   The finite-depth child resources are exactly the ordinary HH18 noisy
--   resource family at the explicitly witnessed next physical rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L286-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L286-L298

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

theorem QEC.Distillation.HH18Parameterized.routedDepthChildResources_eq_noisyResources {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthChildResources h hdegree state port hhalf =
      noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf) := by sorry
