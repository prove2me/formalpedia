-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsShortPreexact_biprod
-- name    : PretorsionImageClosed.Statement.IsShortPreexact.biprod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:07:11.535806+00:00
-- url     : https://prove2.me/theorems/658dcb8e-ae0d-4565-b0c1-6c4106abb824
-- title:
--   Is Short Preexact: biprod
-- statement:
--   The Is Short Preexact construction uses the biprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean#L108-L112
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/DirectSums.lean#L108-L112

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

theorem PretorsionImageClosed.Statement.IsShortPreexact.biprod {T₁ X₁ F₁ T₂ X₂ F₂ : C} {u₁ : T₁ ⟶ X₁} {v₁ : X₁ ⟶ F₁}
    {u₂ : T₂ ⟶ X₂} {v₂ : X₂ ⟶ F₂} (h₁ : IsShortPreexact Zs.prop u₁ v₁)
    (h₂ : IsShortPreexact Zs.prop u₂ v₂) :
    IsShortPreexact Zs.prop (biprod.map u₁ u₂) (biprod.map v₁ v₂) := by sorry
