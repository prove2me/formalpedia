-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_lowerSecond_le_F
-- name    : PretorsionImageClosed.Statement.lowerSecond_le_F
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:07:25.328909+00:00
-- url     : https://prove2.me/theorems/7d4a9b26-d8f4-4bdb-b808-443fccb14d1b
-- title:
--   Statement: lower Second le F
-- statement:
--   Corollary 4.5, second half: `F⁻(Z)` is contained in the second component
--   of every realization of `Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L257-L264
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L257-L264

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

theorem PretorsionImageClosed.Statement.lowerSecond_le_F : (lowerSecond Z hZ).prop ≤ P.F.prop := by sorry
