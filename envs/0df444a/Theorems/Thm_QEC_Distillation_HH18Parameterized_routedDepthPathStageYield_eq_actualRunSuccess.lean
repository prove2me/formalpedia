-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathStageYield_eq_actualRunSuccess
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathStageYield_eq_actualRunSuccess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:05:25.648863+00:00
-- url     : https://prove2.me/theorems/ceb832b2-6b94-4f04-ada2-402eb92fc936
-- title:
--   HH18 Parameterized: routed Depth Path Stage Yield eq actual Run Success
-- statement:
--   Each finite stage yield is exactly the success probability of its actual
--   parameterized routed-depth run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L64-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L64-L71

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathStageYield_eq_actualRunSuccess {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    (routedDepthPathStageYield h hdegree epsilon hsmall depth path stage : ℝ) =
      (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability := by sorry
