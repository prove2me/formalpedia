-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isShortPreexact_id
-- name    : PretorsionImageClosed.Statement.isShortPreexact_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:09:01.378279+00:00
-- url     : https://prove2.me/theorems/190bc08d-1f65-45d2-bba0-d8412bd0e89e
-- title:
--   Statement: is Short Preexact id
-- statement:
--   The identity sequence of an object of `Zs` is short preexact.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean#L148-L154
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean#L148-L154

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

theorem PretorsionImageClosed.Statement.isShortPreexact_id {X : C} (hX : Zs.prop X) :
    IsShortPreexact Zs.prop (𝟙 X) (𝟙 X) := by sorry
