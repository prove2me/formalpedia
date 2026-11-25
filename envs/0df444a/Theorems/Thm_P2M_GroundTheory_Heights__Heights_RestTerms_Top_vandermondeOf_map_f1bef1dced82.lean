-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_map_f1bef1dced82
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_map_f1bef1dced82
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:35:56.48181+00:00
-- url     : https://prove2.me/theorems/fa7faaa4-54ec-416b-b7a7-315df147a615
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top vandermonde Of map f1bef1dced82: P2 M Ground Theory Heights  Heights Rest Terms Top vandermonde Of map f1bef1dced82
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top vandermonde Of map f1bef1dced82 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top vandermonde Of map f1bef1dced82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L128-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_map_f1bef1dced82 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (v : Fin m → R) : φ (vandermondeOf v) = vandermondeOf (fun i => φ (v i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«vandermondeOf_map» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_vandermondeOf_map_f1bef1dced82
