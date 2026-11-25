-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsShortPreexact_of_iso
-- name    : PretorsionImageClosed.Statement.IsShortPreexact.of_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:07:47.952812+00:00
-- url     : https://prove2.me/theorems/eafcb930-c893-59af-92b5-fbd37f0bdda5
-- title:
--   Is Short Preexact: of iso
-- statement:
--   Transport of a short preexact sequence along an isomorphism of the middle term.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean#L115-L145
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean#L115-L145

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_DirectSums
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] {Zs : Subcategory C}

theorem PretorsionImageClosed.Statement.IsShortPreexact.of_iso {T X X' F : C} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsShortPreexact Zs.prop u v) (e : X ≅ X') :
    IsShortPreexact Zs.prop (u ≫ e.hom) (e.inv ≫ v) := by sorry
