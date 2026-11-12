-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildRun_eq_resourceDecodedRun
-- name    : QEC.Distillation.HH18Parameterized.depthTwoChildRun_eq_resourceDecodedRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:49:50.52592+00:00
-- url     : https://prove2.me/theorems/654ea01b-9d32-4b5a-bd38-9faa647b4a47
-- title:
--   HH18 Parameterized: depth Two Child Run eq resource Decoded Run
-- statement:
--   The routed actual child run is exactly the ordinary one-level
--   parameterized run at its derived physical input rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L239-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L239-L247

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

theorem QEC.Distillation.HH18Parameterized.depthTwoChildRun_eq_resourceDecodedRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :
    depthTwoChildRun h hdegree epsilon child hhalf =
      resourceDecodedRun h hdegree (noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf)) := by sorry
