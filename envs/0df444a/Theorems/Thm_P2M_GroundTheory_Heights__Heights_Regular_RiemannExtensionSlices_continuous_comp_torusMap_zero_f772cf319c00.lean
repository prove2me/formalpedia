-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_continuous_comp_torusMap_zero_f772cf319c00
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_continuous_comp_torusMap_zero_f772cf319c00
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:20.784494+00:00
-- url     : https://prove2.me/theorems/e52b297e-f0b2-4c5d-a35e-221ca68ebd27
-- title:
--   P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices continuous comp torus Map zero f772cf319c00: P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices continuous comp t
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices continuous comp torus Map zero f772cf319c00 construction uses the P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices continuous comp torus Map zero f772cf319c00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L24-L30

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_continuous_comp_torusMap_zero_f772cf319c00 {n : ℕ} {G : (Fin n → ℂ) → ℂ}
    (hd : ∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) → DifferentiableAt ℂ G ζ)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous fun θ => G (torusMap (0 : Fin n → ℂ) (fun _ => r) θ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RiemannExtensionSlices».«continuous_comp_torusMap_zero» := P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_continuous_comp_torusMap_zero_f772cf319c00
