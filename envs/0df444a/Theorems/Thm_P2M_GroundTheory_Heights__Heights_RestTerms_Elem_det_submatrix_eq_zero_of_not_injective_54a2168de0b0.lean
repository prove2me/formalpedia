-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_submatrix_eq_zero_of_not_injective_54a2168de0b0
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_submatrix_eq_zero_of_not_injective_54a2168de0b0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:58.992635+00:00
-- url     : https://prove2.me/theorems/3e9dc96f-62d2-45a7-964a-d56e636ba41e
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem det submatrix eq zero of not injective 54a2168de0b0: P2 M Ground Theory Heights  Heights Rest Terms Elem det submatrix eq zero of not injective 54a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem det submatrix eq zero of not injective 54a2168de0b0 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem det submatrix eq zero of not injective 54a2168de0b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean#L45-L49

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_submatrix_eq_zero_of_not_injective_54a2168de0b0 {p : ℕ} (A : Matrix (Fin p) κ R)
    (φ : Fin p → κ) (h : ¬ Function.Injective φ) : (A.submatrix id φ).det = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«det_submatrix_eq_zero_of_not_injective» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_submatrix_eq_zero_of_not_injective_54a2168de0b0
