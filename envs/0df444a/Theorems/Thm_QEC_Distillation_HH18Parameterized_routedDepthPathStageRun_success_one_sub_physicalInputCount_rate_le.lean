-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathStageRun_success_one_sub_physicalInputCount_rate_le
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathStageRun_success_one_sub_physicalInputCount_rate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:06:42.25597+00:00
-- url     : https://prove2.me/theorems/e06eeac2-8389-4d9c-8dd3-1bf3400edc3f
-- title:
--   HH18 Parameterized: routed Depth Path Stage Run success one sub physical Input Count rate le
-- statement:
--   The all-zero accepted physical-error branch and Bernoulli's inequality
--   give a literal one-stage success lower bound at every reached path rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L101-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L101-L127

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathStageRun_success_one_sub_physicalInputCount_rate_le
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    1 - (physicalInputCount m w : ℝ) *
        (routedDepthPathRate h hdegree epsilon hsmall stage.1
          (routedDepthPathStagePath m w depth path stage)).1 ≤
      (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability := by sorry
