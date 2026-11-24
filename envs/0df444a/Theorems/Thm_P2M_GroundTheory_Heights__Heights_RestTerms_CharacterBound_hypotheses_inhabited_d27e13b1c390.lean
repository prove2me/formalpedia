-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CharacterBound_hypotheses_inhabited_d27e13b1c390
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CharacterBound_hypotheses_inhabited_d27e13b1c390
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:19.336012+00:00
-- url     : https://prove2.me/theorems/d51c2748-f810-424a-ae43-cf020a699eab
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Character Bound hypotheses inhabited d27e13b1c390: P2 M Ground Theory Heights  Heights Rest Terms Character Bound hypotheses inhabited d27e13b1c390
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Character Bound hypotheses inhabited d27e13b1c390 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Character Bound hypotheses inhabited d27e13b1c390 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Statements.lean#L405-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Statements.lean#L405-L409

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
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
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CharacterBound_hypotheses_inhabited_d27e13b1c390 :
    Antitone (![2, 1] : Fin 2 → ℕ) ∧ ∀ q ∈ [2, 1], 1 ≤ q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CharacterBound».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_RestTerms_CharacterBound_hypotheses_inhabited_d27e13b1c390
