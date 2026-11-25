-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_comp_iso_right
-- name    : PretorsionImageClosed.Statement.IsPrekernel.comp_iso_right
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:56:19.669986+00:00
-- url     : https://prove2.me/theorems/c42aba46-1a5d-4ed1-9390-000e30f2330e
-- title:
--   Is Prekernel: comp iso right
-- statement:
--   The Is Prekernel construction uses the comp iso right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L61-L66
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L61-L66

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

theorem PretorsionImageClosed.Statement.IsPrekernel.comp_iso_right {T X F F' : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v)
    (e : F ≅ F') : IsPrekernel Z u (v ≫ e.hom) := by sorry
