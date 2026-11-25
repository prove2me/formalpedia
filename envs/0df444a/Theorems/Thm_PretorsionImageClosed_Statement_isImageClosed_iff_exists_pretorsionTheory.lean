-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isImageClosed_iff_exists_pretorsionTheory
-- name    : PretorsionImageClosed.Statement.isImageClosed_iff_exists_pretorsionTheory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:06:53.326108+00:00
-- url     : https://prove2.me/theorems/a767a0c2-c34f-4387-9075-18b4b60dc62b
-- title:
--   Statement: is Image Closed iff exists pretorsion Theory
-- statement:
--   Theorem 4.4, (1) ⇔ (3).
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L225-L233
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L225-L233

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

theorem PretorsionImageClosed.Statement.isImageClosed_iff_exists_pretorsionTheory (Z : Subcategory C) :
    Z.IsImageClosed ↔ ∃ P : PretorsionTheory C, P.middle = Z.prop := by sorry
