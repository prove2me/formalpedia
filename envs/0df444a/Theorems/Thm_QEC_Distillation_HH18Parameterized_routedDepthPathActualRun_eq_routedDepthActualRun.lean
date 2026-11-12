-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathActualRun_eq_routedDepthActualRun
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathActualRun_eq_routedDepthActualRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:44:52.422467+00:00
-- url     : https://prove2.me/theorems/3b1855fd-13ef-4a8c-9265-af163e737979
-- title:
--   HH18 Parameterized: routed Depth Path Actual Run eq routed Depth Actual Run
-- statement:
--   The direct path run is exactly the run indexed by its packaged actual
--   routed-depth state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L787-L795
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L787-L795

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathActualRun_eq_routedDepthActualRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    routedDepthPathActualRun h hdegree epsilon hsmall depth path =
      routedDepthActualRun h hdegree
        (routedDepthPathStatePackage h hdegree epsilon hsmall depth path).state := by sorry
