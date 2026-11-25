-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPrecokernel_of_eq
-- name    : PretorsionImageClosed.Statement.IsPrecokernel.of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:24:42.432944+00:00
-- url     : https://prove2.me/theorems/d423fc85-cf7e-46d1-963d-774783d8c59c
-- title:
--   Is Precokernel: of eq
-- statement:
--   The Is Precokernel construction uses the of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L86-L87
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L86-L87

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

theorem PretorsionImageClosed.Statement.IsPrecokernel.of_eq {T X F : C} {u : T ⟶ X} {v v' : X ⟶ F} (h : IsPrecokernel Z u v)
    (e : v = v') : IsPrecokernel Z u v' := by sorry
