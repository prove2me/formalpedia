-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_cover_le_volume_thickening_5b3271255eb1
-- name    : P2M_GroundTheory_Heights__Heights_exists_cover_le_volume_thickening_5b3271255eb1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:33.265002+00:00
-- url     : https://prove2.me/theorems/eaff8af5-99da-413f-b25b-ef0efc5cee98
-- title:
--   P2 M Ground Theory Heights  Heights exists cover le volume thickening 5b3271255eb1: P2 M Ground Theory Heights  Heights exists cover le volume thickening 5b3271255eb1
-- statement:
--   The P2 M Ground Theory Heights  Heights exists cover le volume thickening 5b3271255eb1 construction uses the P2 M Ground Theory Heights  Heights exists cover le volume thickening 5b3271255eb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSmallSetBallCover.lean#L19-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSmallSetBallCover.lean#L19-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover
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
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_exists_cover_le_volume_thickening_5b3271255eb1 {n : ℕ} {A : Set (Fin n → ℂ)} (hA : IsCompact A) {r : ℝ}
    (hr : 0 < r) : ∃ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ A ∧ A ⊆ ⋃ c ∈ T, ball c r ∧
      (T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n ≤ (volume (thickening r A)).toReal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_cover_le_volume_thickening» := P2M_GroundTheory_Heights__Heights_exists_cover_le_volume_thickening_5b3271255eb1
