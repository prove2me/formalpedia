-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cauchy_torus_off_axes_2daaebd2de5c
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cauchy_torus_off_axes_2daaebd2de5c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:25.235923+00:00
-- url     : https://prove2.me/theorems/d63894d8-cfea-4d61-8f51-7bcb0acd7856
-- title:
--   P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cauchy torus off axes 2daaebd2de5c: P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cauchy torus off axes 2daa
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cauchy torus off axes 2daaebd2de5c construction uses the P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cauchy torus off axes 2daaebd2de5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L46-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L46-L142

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cauchy_torus_off_axes_2daaebd2de5c : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ),
    (∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) → DifferentiableAt ℂ G ζ) →
    (∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → z j ≠ 0) →
      ∃ c : ℂ, Tendsto (fun x : ℂ => G (Function.update z i x)) (𝓝[≠] 0) (𝓝 c)) →
    ∀ r : ℝ, 0 < r → r < 1 → ∀ z ∈ ball (0 : Fin n → ℂ) r, (∀ i, z i ≠ 0) →
    (∯ ζ in T(0, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * G ζ) = (2 * π * I) ^ n * G z
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RiemannExtensionSlices».«cauchy_torus_off_axes» := P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cauchy_torus_off_axes_2daaebd2de5c
