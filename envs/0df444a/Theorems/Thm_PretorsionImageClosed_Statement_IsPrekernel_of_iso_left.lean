-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_of_iso_left
-- name    : PretorsionImageClosed.Statement.IsPrekernel.of_iso_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:56:06.05581+00:00
-- url     : https://prove2.me/theorems/c5dec744-42bf-4f9a-8af8-1687951f782d
-- title:
--   Is Prekernel: of iso left
-- statement:
--   The Is Prekernel construction uses the of iso left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L53-L59
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L53-L59

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}

theorem PretorsionImageClosed.Statement.IsPrekernel.of_iso_left {T T' X F : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v)
    (e : T' ≅ T) : IsPrekernel Z (e.hom ≫ u) v := by sorry
