-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleActualOutputError_exists_path
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleActualOutputError_exists_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:49:48.804637+00:00
-- url     : https://prove2.me/theorems/981b285f-7e19-4741-bd13-817854c6dc8d
-- title:
--   HH18 Parameterized: routed Depth Schedule Actual Output Error exists path
-- statement:
--   The finite reached-error maximum is attained by one literal routed path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L64-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L64-L77

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleActualOutputError_exists_path {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    ∃ path : routedDepthOutputSlots m w depth,
      routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth =
        (routedDepthPathRate h hdegree epsilon hsmall depth path).1 := by sorry
