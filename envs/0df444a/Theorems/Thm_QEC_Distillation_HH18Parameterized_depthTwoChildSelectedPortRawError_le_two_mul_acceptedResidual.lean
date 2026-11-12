-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildSelectedPortRawError_le_two_mul_acceptedResidual
-- name    : QEC.Distillation.HH18Parameterized.depthTwoChildSelectedPortRawError_le_two_mul_acceptedResidual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:08:49.001824+00:00
-- url     : https://prove2.me/theorems/f72aa68c-d192-4762-abf7-b794666ac772
-- title:
--   HH18 Parameterized: depth Two Child Selected Port Raw Error le two mul accepted Residual
-- statement:
--   The second application of the compiled selected-port error bridge, at the
--   actual derived child input rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L309-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L309-L319

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

theorem QEC.Distillation.HH18Parameterized.depthTwoChildSelectedPortRawError_le_two_mul_acceptedResidual
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) :
    depthTwoChildSelectedPortRawError h hdegree epsilon child hhalf port ≤
      2 * acceptedResidualError h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) := by sorry
