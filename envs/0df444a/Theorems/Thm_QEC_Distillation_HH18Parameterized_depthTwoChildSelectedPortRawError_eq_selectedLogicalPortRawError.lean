-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildSelectedPortRawError_eq_selectedLogicalPortRawError
-- name    : QEC.Distillation.HH18Parameterized.depthTwoChildSelectedPortRawError_eq_selectedLogicalPortRawError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:06:55.393087+00:00
-- url     : https://prove2.me/theorems/8483d9ab-9175-430a-87a2-2f96aae8a479
-- title:
--   HH18 Parameterized: depth Two Child Selected Port Raw Error eq selected Logical Port Raw Error
-- statement:
--   The selected child Born error is exactly the one-level selected-port
--   Born error at the child's derived physical input rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L295-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L295-L305

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

theorem QEC.Distillation.HH18Parameterized.depthTwoChildSelectedPortRawError_eq_selectedLogicalPortRawError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) :
    depthTwoChildSelectedPortRawError h hdegree epsilon child hhalf port =
      selectedLogicalPortRawError h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) port := by sorry
