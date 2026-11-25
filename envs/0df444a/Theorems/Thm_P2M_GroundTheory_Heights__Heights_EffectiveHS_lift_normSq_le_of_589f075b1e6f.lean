-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_of_589f075b1e6f
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_of_589f075b1e6f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:25.285992+00:00
-- url     : https://prove2.me/theorems/5d57ff5d-7549-52c8-b0fa-6c7144e6162a
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS lift norm Sq le of 589f075b1e6f: P2 M Ground Theory Heights  Heights Effective HS lift norm Sq le of 589f075b1e6f
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS lift norm Sq le of 589f075b1e6f construction uses the P2 M Ground Theory Heights  Heights Effective HS lift norm Sq le of 589f075b1e6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L131-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L131-L167

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_of_589f075b1e6f {X ι : Type*} [MeasurableSpace X] (μ : Measure X) [Fintype ι]
    (u Ft : ι → X → ℂ) (r G : ι → ℝ) (K B N : ℝ) (hB : 0 ≤ B)
    (hu : ∀ i x, ‖u i x‖ ≤ r i) (hFt : ∀ i, Integrable (fun x => ‖Ft i x‖ ^ 2) μ)
    (hL : ∀ i, ∫ x, ‖Ft i x‖ ^ 2 ∂μ ≤ K * G i ^ 2)
    (hN : N ^ 2 ≤ B * ∫ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ∂μ) :
    N ^ 2 ≤ B * K * (Fintype.card ι) * ∑ i, r i ^ 2 * G i ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«lift_normSq_le_of» := P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_of_589f075b1e6f
