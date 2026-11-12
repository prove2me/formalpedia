-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathLoss_sum_le_one_sixth
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathLoss_sum_le_one_sixth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:05:11.227476+00:00
-- url     : https://prove2.me/theorems/963c51dc-2b3b-408a-88d8-da25d838fb3e
-- title:
--   HH18 Parameterized: routed Depth Path Loss sum le one sixth
-- statement:
--   The physical-input-weighted losses along every literal finite path are
--   summable by the same global envelope budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L170-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L170-L192

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathLoss_sum_le_one_sixth {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    ∑ stage : Fin depth, (physicalInputCount m w : ℝ) *
      (routedDepthPathRate h hdegree epsilon hsmall stage.1
        (routedDepthPathStagePath m w depth path stage)).1 ≤ 1 / 6 := by sorry
