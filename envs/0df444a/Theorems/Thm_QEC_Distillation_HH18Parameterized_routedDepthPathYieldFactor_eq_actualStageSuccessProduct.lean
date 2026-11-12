-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathYieldFactor_eq_actualStageSuccessProduct
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathYieldFactor_eq_actualStageSuccessProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:40:06.753861+00:00
-- url     : https://prove2.me/theorems/5819a5b7-4689-46c1-99e1-c1ce57595c62
-- title:
--   HH18 Parameterized: routed Depth Path Yield Factor eq actual Stage Success Product
-- statement:
--   The finite accounting product is literally the product of success
--   probabilities of the actual path-indexed stage runs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L84-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L84-L97

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathYieldFactor_eq_actualStageSuccessProduct {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) =
      ∏ stage : Fin depth,
        (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability := by sorry
