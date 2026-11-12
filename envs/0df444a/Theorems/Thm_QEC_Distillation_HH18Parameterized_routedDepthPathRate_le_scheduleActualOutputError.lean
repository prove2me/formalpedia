-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_le_scheduleActualOutputError
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathRate_le_scheduleActualOutputError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:50:34.040523+00:00
-- url     : https://prove2.me/theorems/2c7d987b-d03a-4db9-a72e-0da95758b834
-- title:
--   HH18 Parameterized: routed Depth Path Rate le schedule Actual Output Error
-- statement:
--   Every literal path rate is included in the reached finite maximum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L50-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Schedule.lean#L50-L61

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathRate_le_scheduleActualOutputError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthPathRate h hdegree epsilon hsmall depth path).1 ≤
      routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth := by sorry
