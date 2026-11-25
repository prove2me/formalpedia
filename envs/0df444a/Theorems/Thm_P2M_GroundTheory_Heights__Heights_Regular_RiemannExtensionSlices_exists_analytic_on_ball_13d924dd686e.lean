-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_exists_analytic_on_ball_13d924dd686e
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_exists_analytic_on_ball_13d924dd686e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:52.706929+00:00
-- url     : https://prove2.me/theorems/68b021ba-c83d-401b-a7e4-a79811769056
-- title:
--   P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices exists analytic on ball 13d924dd686e: P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices exists analytic on ball
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices exists analytic on ball 13d924dd686e construction uses the P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices exists analytic on ball 13d924dd686e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L197-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L197-L210

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_exists_analytic_on_ball_13d924dd686e {n : ℕ} {G : (Fin n → ℂ) → ℂ}
    (hd : ∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) → DifferentiableAt ℂ G ζ)
    (hlim : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → z j ≠ 0) →
      ∃ c : ℂ, Tendsto (fun x : ℂ => G (Function.update z i x)) (𝓝[≠] 0) (𝓝 c))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ Φ : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Φ (ball 0 r) ∧
      ∀ z ∈ ball (0 : Fin n → ℂ) r, (∀ i, z i ≠ 0) → Φ z = G z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RiemannExtensionSlices».«exists_analytic_on_ball» := P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_exists_analytic_on_ball_13d924dd686e
