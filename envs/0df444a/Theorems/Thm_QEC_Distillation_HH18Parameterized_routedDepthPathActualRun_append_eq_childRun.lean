-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathActualRun_append_eq_childRun
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathActualRun_append_eq_childRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:45:56.31316+00:00
-- url     : https://prove2.me/theorems/314340fa-9c64-41f7-b660-b67dee405172
-- title:
--   HH18 Parameterized: routed Depth Path Actual Run append eq child Run
-- statement:
--   Appending a selected port constructs the literal routed child run of the
--   actual preceding path state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L816-L829
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L816-L829

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathActualRun_append_eq_childRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    routedDepthPathActualRun h hdegree epsilon hsmall (depth + 1)
      (routedDepthOutputPathAppend m w depth path port) =
      routedDepthChildRun h hdegree
        (routedDepthPathState h hdegree epsilon hsmall depth path) port
        (routedDepthPathNextHalf h hdegree epsilon hsmall path port) := by sorry
