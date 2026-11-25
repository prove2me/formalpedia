-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_far_point_77b620157daf
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_far_point_77b620157daf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:01.8758+00:00
-- url     : https://prove2.me/theorems/2b3ffa84-3544-4ce2-8f47-bf72d351962a
-- title:
--   P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound exists far point 77b620157daf: P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound exists far point 77b620157daf
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound exists far point 77b620157daf construction uses the P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound exists far point 77b620157daf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PPolyMaxLowerBound.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PPolyMaxLowerBound.lean#L41-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PPolyMaxLowerBound
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
open Metric Set
open ReciprocityTheory.AnForm.A (polyMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_far_point_77b620157daf {D : ℕ} (z : Fin D → ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ y ∈ closedBall z t, ∀ i, t / 2 ≤ ‖y i‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PolyMaxLowerBound».«exists_far_point» := P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_far_point_77b620157daf
