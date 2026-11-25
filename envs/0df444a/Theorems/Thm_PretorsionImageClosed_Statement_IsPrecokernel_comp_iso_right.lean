-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPrecokernel_comp_iso_right
-- name    : PretorsionImageClosed.Statement.IsPrecokernel.comp_iso_right
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:56:15.5663+00:00
-- url     : https://prove2.me/theorems/051aa940-e023-4e10-b652-cd611abccede
-- title:
--   Is Precokernel: comp iso right
-- statement:
--   The Is Precokernel construction uses the comp iso right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L75-L81
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L75-L81

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

theorem PretorsionImageClosed.Statement.IsPrecokernel.comp_iso_right {T X F F' : C} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsPrecokernel Z u v) (e : F ≅ F') : IsPrecokernel Z u (v ≫ e.hom) := by sorry
