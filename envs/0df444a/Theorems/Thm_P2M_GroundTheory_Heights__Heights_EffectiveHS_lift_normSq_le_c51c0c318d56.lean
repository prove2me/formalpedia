-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_c51c0c318d56
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_c51c0c318d56
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:51.400734+00:00
-- url     : https://prove2.me/theorems/34da0157-e38f-4ef0-856e-ee090d870d8f
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS lift norm Sq le c51c0c318d56: P2 M Ground Theory Heights  Heights Effective HS lift norm Sq le c51c0c318d56
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS lift norm Sq le c51c0c318d56 construction uses the P2 M Ground Theory Heights  Heights Effective HS lift norm Sq le c51c0c318d56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L184-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L184-L194

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open MeasureTheory

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_c51c0c318d56 {X ι : Type*} [MeasurableSpace X] (μ : Measure X) [Fintype ι]
    (D T : ℕ) (β r : ℝ) (hβ : 0 ≤ β) (u Ft : ι → X → ℂ) (rα G : ι → ℝ) (N : ℝ)
    (hu : ∀ i x, ‖u i x‖ ≤ rα i) (hFt : ∀ i, Integrable (fun x => ‖Ft i x‖ ^ 2) μ)
    (hL : ∀ i, ∫ x, ‖Ft i x‖ ^ 2 ∂μ ≤ 140 * cD D * r ^ (2 * D) * G i ^ 2)
    (hN : N ^ 2 ≤ β ^ (T + D + 1) * ∫ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ∂μ) :
    N ^ 2 ≤ (β ^ (T + D + 1) * 140 * cD D * (Fintype.card ι) * r ^ (2 * D)) *
      ∑ i, rα i ^ 2 * G i ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«lift_normSq_le» := P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_c51c0c318d56
