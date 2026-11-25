-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_biprod_lift
-- name    : PretorsionImageClosed.Statement.IsTrivial.biprod_lift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:02:05.486023+00:00
-- url     : https://prove2.me/theorems/9aed0fef-3dd5-55c9-bb2c-1bdef3cbbe1d
-- title:
--   Is Trivial: biprod lift
-- statement:
--   The Is Trivial construction uses the biprod lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean#L38-L44
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean#L38-L44

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

theorem PretorsionImageClosed.Statement.IsTrivial.biprod_lift {W Y₁ Y₂ : C} {f₁ : W ⟶ Y₁} {f₂ : W ⟶ Y₂}
    (h₁ : IsTrivial Zs.prop f₁) (h₂ : IsTrivial Zs.prop f₂) :
    IsTrivial Zs.prop (biprod.lift f₁ f₂) := by sorry
