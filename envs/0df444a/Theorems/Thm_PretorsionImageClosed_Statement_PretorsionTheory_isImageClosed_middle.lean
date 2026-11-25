-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isImageClosed_middle
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.isImageClosed_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:06:59.999507+00:00
-- url     : https://prove2.me/theorems/185f2c6d-392f-41e8-bce7-2fcf05a02ca2
-- title:
--   Pretorsion Theory: is Image Closed middle
-- statement:
--   Theorem 4.4, (3) ⇒ (1): the intersection of a pretorsion theory is
--   image-closed.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L219-L222
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/TheoremA.lean#L219-L222

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.isImageClosed_middle (P : PretorsionTheory C) :
    (P.T ⊓ P.F).IsImageClosed := by sorry
