-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_mul_expand_87daf8b7a418
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_mul_expand_87daf8b7a418
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:19:01.843875+00:00
-- url     : https://prove2.me/theorems/c79ab2fc-dcdc-418b-99f6-87569a46baa2
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem det mul expand 87daf8b7a418: P2 M Ground Theory Heights  Heights Rest Terms Elem det mul expand 87daf8b7a418
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem det mul expand 87daf8b7a418 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem det mul expand 87daf8b7a418 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean#L35-L43

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_mul_expand_87daf8b7a418 [Fintype κ] {p : ℕ} (A : Matrix (Fin p) κ R) (B : Matrix κ (Fin p) R) :
    (A * B).det = ∑ φ : Fin p → κ, (A.submatrix id φ).det * ∏ i, B (φ i) i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«det_mul_expand» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_mul_expand_87daf8b7a418
