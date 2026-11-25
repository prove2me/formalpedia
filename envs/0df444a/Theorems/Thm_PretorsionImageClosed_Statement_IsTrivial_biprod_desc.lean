-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_biprod_desc
-- name    : PretorsionImageClosed.Statement.IsTrivial.biprod_desc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:02:16.315261+00:00
-- url     : https://prove2.me/theorems/20d3d4c7-b8a6-4269-9ec6-bdf6c81e7ef7
-- title:
--   Is Trivial: biprod desc
-- statement:
--   The Is Trivial construction uses the biprod desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean#L46-L52
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean#L46-L52

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

theorem PretorsionImageClosed.Statement.IsTrivial.biprod_desc {X₁ X₂ Y : C} {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y}
    (h₁ : IsTrivial Zs.prop f₁) (h₂ : IsTrivial Zs.prop f₂) :
    IsTrivial Zs.prop (biprod.desc f₁ f₂) := by sorry
