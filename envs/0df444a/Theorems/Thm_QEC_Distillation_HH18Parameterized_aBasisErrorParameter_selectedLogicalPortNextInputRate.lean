-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_aBasisErrorParameter_selectedLogicalPortNextInputRate
-- name    : QEC.Distillation.HH18Parameterized.aBasisErrorParameter_selectedLogicalPortNextInputRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:06:09.303569+00:00
-- url     : https://prove2.me/theorems/23887b04-58c5-4db9-9621-451b0ec8b2a6
-- title:
--   HH18 Parameterized: a Basis Error Parameter selected Logical Port Next Input Rate
-- statement:
--   The A-basis parameter of the domain-certified child input is exactly the
--   literal measured selected-port parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L103-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DepthTwoRouting.lean#L103-L110

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

theorem QEC.Distillation.HH18Parameterized.aBasisErrorParameter_selectedLogicalPortNextInputRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2) :
    aBasisErrorParameter
      (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf) =
      selectedLogicalPortRawParameter h hdegree epsilon port := by sorry
