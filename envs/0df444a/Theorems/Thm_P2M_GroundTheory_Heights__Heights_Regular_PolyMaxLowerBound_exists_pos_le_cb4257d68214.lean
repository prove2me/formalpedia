-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_pos_le_cb4257d68214
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_pos_le_cb4257d68214
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:17:50.446469+00:00
-- url     : https://prove2.me/theorems/f705513d-4fcd-59b3-bf35-1279be7f8eb1
-- title:
--   P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound exists pos le cb4257d68214: P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound exists pos le cb4257d68214
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound exists pos le cb4257d68214 construction uses the P2 M Ground Theory Heights  Heights Regular Poly Max Lower Bound exists pos le cb4257d68214 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PPolyMaxLowerBound.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PPolyMaxLowerBound.lean#L13-L18

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

theorem P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_pos_le_cb4257d68214 {n : ℕ} (f : Fin n → ℝ) (hf : ∀ j, 0 < f j) :
    ∃ δ, 0 < δ ∧ ∀ j, δ ≤ f j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PolyMaxLowerBound».«exists_pos_le» := P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_pos_le_cb4257d68214
