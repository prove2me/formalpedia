-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_append_eq_nextInputRate
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathRate_append_eq_nextInputRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:35:05.886221+00:00
-- url     : https://prove2.me/theorems/ff0a8e79-7954-4ce7-a990-903c81e0bb01
-- title:
--   HH18 Parameterized: routed Depth Path Rate append eq next Input Rate
-- statement:
--   The selector successor is the actual domain-certified next input rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L798-L812
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L798-L812

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathRate_append_eq_nextInputRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
      (routedDepthOutputPathAppend m w depth path port) =
        selectedLogicalPortNextInputRate h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall depth path) port
          (routedDepthPathNextHalf h hdegree epsilon hsmall path port) := by sorry
