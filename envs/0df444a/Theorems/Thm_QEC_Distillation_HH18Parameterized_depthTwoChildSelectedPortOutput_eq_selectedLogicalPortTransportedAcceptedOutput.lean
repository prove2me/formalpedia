-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildSelectedPortOutput_eq_selectedLogicalPortTransportedAcceptedOutput
-- name    : QEC.Distillation.HH18Parameterized.depthTwoChildSelectedPortOutput_eq_selectedLogicalPortTransportedAcceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:07:52.993744+00:00
-- url     : https://prove2.me/theorems/41973415-ea5c-4acd-9fa6-561f3580230b
-- title:
--   HH18 Parameterized: depth Two Child Selected Port Output eq selected Logical Port Transported Accepted Output
-- statement:
--   The actual selected child output is the established one-level selected
--   output at the derived physical input rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L271-L281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L271-L281

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

theorem QEC.Distillation.HH18Parameterized.depthTwoChildSelectedPortOutput_eq_selectedLogicalPortTransportedAcceptedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) :
    depthTwoChildSelectedPortOutput h hdegree epsilon child hhalf port =
      selectedLogicalPortTransportedAcceptedOutput h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) port := by sorry
