-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthSuccessorRate_le_two_mul_acceptedResidual
-- name    : QEC.Distillation.HH18Parameterized.routedDepthSuccessorRate_le_two_mul_acceptedResidual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:44:45.931025+00:00
-- url     : https://prove2.me/theorems/9a64c0e7-6b27-4fcf-8d5e-13d0f85f6dcc
-- title:
--   HH18 Parameterized: routed Depth Successor Rate le two mul accepted Residual
-- statement:
--   The recurrence's next physical rate inherits the compiled selected-port
--   residual bridge directly, with no target-error or asymptotic conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L371-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L371-L379

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

theorem QEC.Distillation.HH18Parameterized.routedDepthSuccessorRate_le_two_mul_acceptedResidual {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    (selectedLogicalPortNextInputRate h hdegree rate port hhalf).1 ≤
      2 * acceptedResidualError h hdegree rate := by sorry
