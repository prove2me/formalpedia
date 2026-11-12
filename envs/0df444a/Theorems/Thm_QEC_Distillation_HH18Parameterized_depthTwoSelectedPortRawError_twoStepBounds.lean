-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoSelectedPortRawError_twoStepBounds
-- name    : QEC.Distillation.HH18Parameterized.depthTwoSelectedPortRawError_twoStepBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:13:51.31734+00:00
-- url     : https://prove2.me/theorems/147e93ec-1860-4683-ae3e-b6e6376a846a
-- title:
--   HH18 Parameterized: depth Two Selected Port Raw Error two Step Bounds
-- statement:
--   The two depth-two selected-port inequalities are precisely two separate
--   applications of the compiled one-step bridge: first to the parent port, then
--   to a selected child port at the derived input rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L324-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L324-L336

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

theorem QEC.Distillation.HH18Parameterized.depthTwoSelectedPortRawError_twoStepBounds {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree epsilon child ≤
        2 * acceptedResidualError h hdegree epsilon ∧
      depthTwoChildSelectedPortRawError h hdegree epsilon child hhalf port ≤
        2 * acceptedResidualError h hdegree
          (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) := by sorry
