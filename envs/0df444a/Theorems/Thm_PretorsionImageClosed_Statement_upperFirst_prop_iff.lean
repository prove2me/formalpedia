-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_upperFirst_prop_iff
-- name    : PretorsionImageClosed.Statement.upperFirst_prop_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:14:42.029038+00:00
-- url     : https://prove2.me/theorems/28a89737-68a1-59a9-9679-4bdfea302ae5
-- title:
--   Statement: upper First prop iff
-- statement:
--   The Statement construction uses the upper First prop iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L107-L109
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L107-L109

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)

theorem PretorsionImageClosed.Statement.upperFirst_prop_iff (X : C) :
    (upperFirst Z hZ).prop X ↔ ∀ (N : C) (f : X ⟶ N), Z.prop N → Z.prop (imageSubobject f : C) := by sorry
