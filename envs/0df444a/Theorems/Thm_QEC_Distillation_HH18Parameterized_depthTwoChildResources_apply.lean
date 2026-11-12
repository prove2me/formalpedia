-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildResources_apply
-- name    : QEC.Distillation.HH18Parameterized.depthTwoChildResources_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:49:24.969206+00:00
-- url     : https://prove2.me/theorems/6147c6f6-ceb3-4c09-8a94-656b341bfa89
-- title:
--   HH18 Parameterized: depth Two Child Resources apply
-- statement:
--   Each input of a fixed child records its exact fresh-parent provenance:
--   the same child port and the nominated distinct parent index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L204-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L204-L211

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
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

theorem QEC.Distillation.HH18Parameterized.depthTwoChildResources_apply {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (parent : Fin (physicalInputCount m w)) :
    depthTwoChildResources h hdegree epsilon child hhalf parent =
      depthTwoFreshParentNextInput h hdegree epsilon (parent, child) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.depthTwoChildResources_apply
