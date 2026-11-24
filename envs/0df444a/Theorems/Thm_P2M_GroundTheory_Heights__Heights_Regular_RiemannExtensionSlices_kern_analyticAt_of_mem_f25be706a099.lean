-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_kern_analyticAt_of_mem_f25be706a099
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_kern_analyticAt_of_mem_f25be706a099
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:41.08785+00:00
-- url     : https://prove2.me/theorems/324c1e1e-8a1c-4367-b15a-42cde8d82cf8
-- title:
--   P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices kern analytic At of mem f25be706a099: P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices kern analytic At of mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices kern analytic At of mem f25be706a099 construction uses the P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices kern analytic At of mem f25be706a099 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L183-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L183-L195

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_kern_analyticAt_of_mem_f25be706a099 {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) {z : Fin n → ℂ}
    (hz : z ∈ ball c r) : AnalyticAt ℂ (kern c r) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RiemannExtensionSlices».«kern_analyticAt_of_mem» := P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_kern_analyticAt_of_mem_f25be706a099
