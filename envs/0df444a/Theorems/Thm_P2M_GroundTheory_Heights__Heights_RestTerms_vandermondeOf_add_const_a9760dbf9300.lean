-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_add_const_a9760dbf9300
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_add_const_a9760dbf9300
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:38.83562+00:00
-- url     : https://prove2.me/theorems/bdb91ef0-c22c-54e4-8d12-527b884f53c6
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of add const a9760dbf9300: P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of add const a9760dbf9300
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of add const a9760dbf9300 construction uses the P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of add const a9760dbf9300 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookTableauCount.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookTableauCount.lean#L57-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookTableauCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_add_const_a9760dbf9300 {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (c : R) :
    vandermondeOf (fun j => v j + c) = vandermondeOf v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«vandermondeOf_add_const» := P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_add_const_a9760dbf9300
