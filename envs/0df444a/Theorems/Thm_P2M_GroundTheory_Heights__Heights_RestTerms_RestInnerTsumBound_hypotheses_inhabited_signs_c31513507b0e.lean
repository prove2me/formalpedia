-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestInnerTsumBound_hypotheses_inhabited_signs_c31513507b0e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestInnerTsumBound_hypotheses_inhabited_signs_c31513507b0e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:20.275268+00:00
-- url     : https://prove2.me/theorems/4067962c-511a-5fc2-9d87-2f52badbc0c2
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Inner Tsum Bound hypotheses inhabited signs c31513507b0e: P2 M Ground Theory Heights  Heights Rest Terms Rest Inner Tsum Bound hypotheses inhabited
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Inner Tsum Bound hypotheses inhabited signs c31513507b0e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Inner Tsum Bound hypotheses inhabited signs c31513507b0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean#L15-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestInnerTsumBound_hypotheses_inhabited_signs_c31513507b0e :
    (2 : ℝ) ≤ 3 ∧ 1 ≤ 2 ∧ ∀ n : ℕ, |(fun n : ℕ => ((-1 : ℝ) ^ n)) n| ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestInnerTsumBound».«hypotheses_inhabited_signs» := P2M_GroundTheory_Heights__Heights_RestTerms_RestInnerTsumBound_hypotheses_inhabited_signs_c31513507b0e
