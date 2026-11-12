-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthSuccessorRate_eq_rawError
-- name    : QEC.Distillation.HH18Parameterized.routedDepthSuccessorRate_eq_rawError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:43:59.943794+00:00
-- url     : https://prove2.me/theorems/44940bbf-e0c2-4bbc-aab9-0db689d19329
-- title:
--   HH18 Parameterized: routed Depth Successor Rate eq raw Error
-- statement:
--   The successor state's HH18 physical input rate is exactly the literal
--   negative-A Born error of its selected parent port.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L360-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L360-L367

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

theorem QEC.Distillation.HH18Parameterized.routedDepthSuccessorRate_eq_rawError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    (selectedLogicalPortNextInputRate h hdegree rate port hhalf).1 =
      selectedLogicalPortRawError h hdegree rate port := by sorry
