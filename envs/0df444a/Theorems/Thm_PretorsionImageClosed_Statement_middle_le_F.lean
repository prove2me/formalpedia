-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_middle_le_F
-- name    : PretorsionImageClosed.Statement.middle_le_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:06:33.362796+00:00
-- url     : https://prove2.me/theorems/69f7c2fe-bd66-4934-aed6-4e0418766449
-- title:
--   Statement: middle le F
-- statement:
--   The Statement construction uses the middle le F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L240-L240
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L240-L240

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
variable {Z hZ}
variable (hZ : Z.IsImageClosed) (P : PretorsionTheory C) (hP : P.middle = Z.prop)
include hP

theorem PretorsionImageClosed.Statement.middle_le_F : Z.prop ≤ P.F.prop := by sorry
