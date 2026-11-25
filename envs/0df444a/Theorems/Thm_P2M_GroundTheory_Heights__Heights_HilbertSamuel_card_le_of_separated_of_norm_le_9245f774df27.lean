-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_card_le_of_separated_of_norm_le_9245f774df27
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_card_le_of_separated_of_norm_le_9245f774df27
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:06.952241+00:00
-- url     : https://prove2.me/theorems/1015c512-dc04-4396-a99c-fb17a77ae0f8
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel card le of separated of norm le 9245f774df27: P2 M Ground Theory Heights  Heights Hilbert Samuel card le of separated of norm le 9245f774df27
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel card le of separated of norm le 9245f774df27 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel card le of separated of norm le 9245f774df27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPacking.lean#L11-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPacking.lean#L11-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPacking
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Metric Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_card_le_of_separated_of_norm_le_9245f774df27 {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (s : Finset W) {lam r : ℝ} (hlam : 0 < lam) (hr : 0 ≤ r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → lam ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (1 + 2 * r / lam) ^ finrank ℝ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«card_le_of_separated_of_norm_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_card_le_of_separated_of_norm_le_9245f774df27
