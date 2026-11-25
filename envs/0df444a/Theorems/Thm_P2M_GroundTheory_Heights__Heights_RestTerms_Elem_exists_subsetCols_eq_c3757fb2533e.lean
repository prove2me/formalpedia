-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_exists_subsetCols_eq_c3757fb2533e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_exists_subsetCols_eq_c3757fb2533e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:19:10.105058+00:00
-- url     : https://prove2.me/theorems/51070b73-4f3a-4617-9f48-878a9c4a3950
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem exists subset Cols eq c3757fb2533e: P2 M Ground Theory Heights  Heights Rest Terms Elem exists subset Cols eq c3757fb2533e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem exists subset Cols eq c3757fb2533e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem exists subset Cols eq c3757fb2533e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean#L31-L33

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_exists_subsetCols_eq_c3757fb2533e {p : ℕ} (S : {s : Finset κ // s.card = p}) {k : κ}
    (hk : k ∈ S.1) : ∃ i, subsetCols S i = k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«exists_subsetCols_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_exists_subsetCols_eq_c3757fb2533e
