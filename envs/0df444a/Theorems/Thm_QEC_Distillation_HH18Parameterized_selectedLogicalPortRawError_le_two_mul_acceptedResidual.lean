-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortRawError_le_two_mul_acceptedResidual
-- name    : QEC.Distillation.HH18Parameterized.selectedLogicalPortRawError_le_two_mul_acceptedResidual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:47:48.042942+00:00
-- url     : https://prove2.me/theorems/251f684b-03bf-4358-a9ac-52cc3c9732e5
-- title:
--   HH18 Parameterized: selected Logical Port Raw Error le two mul accepted Residual
-- statement:
--   The HH18 Parameterized construction uses the selected Logical Port Raw Error le two mul accepted Residual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L536-L548
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L536-L548

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.selectedLogicalPortRawError_le_two_mul_acceptedResidual {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree epsilon port ≤
      2 * acceptedResidualError h hdegree epsilon := by sorry
