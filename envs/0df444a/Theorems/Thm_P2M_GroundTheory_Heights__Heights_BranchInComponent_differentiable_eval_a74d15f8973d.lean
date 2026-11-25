-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchInComponent_differentiable_eval_a74d15f8973d
-- name    : P2M_GroundTheory_Heights__Heights_BranchInComponent_differentiable_eval_a74d15f8973d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:30.996793+00:00
-- url     : https://prove2.me/theorems/bb5e1032-9a8e-4c13-9b29-4ce3cb95fd8b
-- title:
--   P2 M Ground Theory Heights  Heights Branch In Component differentiable eval a74d15f8973d: P2 M Ground Theory Heights  Heights Branch In Component differentiable eval a74d15f8973d
-- statement:
--   The P2 M Ground Theory Heights  Heights Branch In Component differentiable eval a74d15f8973d construction uses the P2 M Ground Theory Heights  Heights Branch In Component differentiable eval a74d15f8973d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchInComponent.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchInComponent.lean#L14-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchInComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Metric Filter Topology Set
noncomputable section
open GroundTheory.Heights₂.Heights.BranchInComponent

theorem P2M_GroundTheory_Heights__Heights_BranchInComponent_differentiable_eval_a74d15f8973d {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => eval x g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BranchInComponent».«differentiable_eval» := P2M_GroundTheory_Heights__Heights_BranchInComponent_differentiable_eval_a74d15f8973d
