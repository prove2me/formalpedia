-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_T_le_upperFirst
-- name    : PretorsionImageClosed.Statement.T_le_upperFirst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:06:29.833201+00:00
-- url     : https://prove2.me/theorems/8f34ca82-7438-430d-9de9-f329f621ede9
-- title:
--   Statement: T le upper First
-- statement:
--   Corollary 4.5, first half: the first component of a realization of `Z`
--   is contained in `T⁺(Z)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L246-L253
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L246-L253

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

theorem PretorsionImageClosed.Statement.T_le_upperFirst : P.T.prop ≤ (upperFirst Z hZ).prop := by sorry
