-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_subsetCols_mem_800373af329f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_subsetCols_mem_800373af329f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:19:00.706151+00:00
-- url     : https://prove2.me/theorems/9e0c2364-3329-45b2-bd10-b2185441e607
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem subset Cols mem 800373af329f: P2 M Ground Theory Heights  Heights Rest Terms Elem subset Cols mem 800373af329f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem subset Cols mem 800373af329f construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem subset Cols mem 800373af329f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean#L27-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Pluecker
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
open Matrix Finset
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem
variable {R : Type*} [CommRing R] {κ : Type*}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_subsetCols_mem_800373af329f {p : ℕ} (S : {s : Finset κ // s.card = p}) (i : Fin p) :
    subsetCols S i ∈ S.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«subsetCols_mem» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_subsetCols_mem_800373af329f
