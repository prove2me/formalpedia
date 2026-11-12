-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildResources_eq_noisyResources
-- name    : QEC.Distillation.HH18Parameterized.depthTwoChildResources_eq_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:51:07.666167+00:00
-- url     : https://prove2.me/theorems/a03b6165-36fe-4714-b831-48c279cb4452
-- title:
--   HH18 Parameterized: depth Two Child Resources eq noisy Resources
-- statement:
--   The actual distinct-parent child resource family is exactly the ordinary
--   parameterized HH18 noisy-resource family at the child's measured rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L215-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L215-L227

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

theorem QEC.Distillation.HH18Parameterized.depthTwoChildResources_eq_noisyResources {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :
    depthTwoChildResources h hdegree epsilon child hhalf =
      noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) := by sorry
