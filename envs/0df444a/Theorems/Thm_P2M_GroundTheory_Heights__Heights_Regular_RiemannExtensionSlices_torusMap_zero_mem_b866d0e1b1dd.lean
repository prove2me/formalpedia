-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_torusMap_zero_mem_b866d0e1b1dd
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_torusMap_zero_mem_b866d0e1b1dd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:54.844052+00:00
-- url     : https://prove2.me/theorems/48861e63-fc8c-4ae7-a093-7ae2bf45aee7
-- title:
--   P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices torus Map zero mem b866d0e1b1dd: P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices torus Map zero mem b866d0e1b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices torus Map zero mem b866d0e1b1dd construction uses the P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices torus Map zero mem b866d0e1b1dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L16-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices

theorem P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_torusMap_zero_mem_b866d0e1b1dd {n : ℕ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ : Fin n → ℝ) :
    torusMap (0 : Fin n → ℂ) (fun _ => r) θ ∈ ball (0 : Fin n → ℂ) 1 ∧
      ∀ i, torusMap (0 : Fin n → ℂ) (fun _ => r) θ i ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RiemannExtensionSlices».«torusMap_zero_mem» := P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_torusMap_zero_mem_b866d0e1b1dd
