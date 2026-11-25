-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_greatestRealization_middle
-- name    : PretorsionImageClosed.Statement.greatestRealization_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:06:01.613926+00:00
-- url     : https://prove2.me/theorems/33f9bfd1-2d25-4097-b3c9-48189102be8b
-- title:
--   Statement: greatest Realization middle
-- statement:
--   The Statement construction uses the greatest Realization middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L212-L213
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L212-L213

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

theorem PretorsionImageClosed.Statement.greatestRealization_middle : (greatestRealization Z hZ).middle = Z.prop := by sorry
