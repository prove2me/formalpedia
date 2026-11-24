-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_not_mem_269c9461ec4e
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_not_mem_269c9461ec4e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:47.80913+00:00
-- url     : https://prove2.me/theorems/e6d98b3b-44d7-4330-af11-608554a99169
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers prod pow not mem 269c9461ec4e: P2 M Ground Theory Heights  Heights Field Numbers prod pow not mem 269c9461ec4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers prod pow not mem 269c9461ec4e construction uses the P2 M Ground Theory Heights  Heights Field Numbers prod pow not mem 269c9461ec4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PExistsForm.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PExistsForm.lean#L23-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_not_mem_269c9461ec4e {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [hP : P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι R) ∉ P) (n : K → ℕ) :
    (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) ∉ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«prod_pow_not_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_not_mem_269c9461ec4e
