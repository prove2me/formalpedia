-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_gmfOut_zero_9add85c2d281
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_gmfOut_zero_9add85c2d281
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:28.976138+00:00
-- url     : https://prove2.me/theorems/c2f4cf0f-69c4-55b2-bf1a-f0fb96541941
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top gmf Out zero 9add85c2d281: P2 M Ground Theory Heights  Heights Rest Terms Top gmf Out zero 9add85c2d281
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top gmf Out zero 9add85c2d281 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top gmf Out zero 9add85c2d281 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L201-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L201-L229

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_gmfOut_zero_9add85c2d281 (f r a : ℕ) (c : SmallBlock) (κ : ℚ) :
    gmfOut f r a c κ 0 (f * (r * a)) =
      C ((Nat.multinomial Finset.univ (fun _ : Fin f => r * a) : ℚ) *
        (blockCoeff 0 (r * a) (rectangle r a) * κ) ^ f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«gmfOut_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_gmfOut_zero_9add85c2d281
