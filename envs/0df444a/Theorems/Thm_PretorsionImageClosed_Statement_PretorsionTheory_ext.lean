-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:22.802173+00:00
-- url     : https://prove2.me/theorems/a68daf55-700b-4484-89a7-b15b15b9f486
-- title:
--   Pretorsion Theory: ext
-- statement:
--   Pretorsion theories with the same components are equal.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L129-L135
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L129-L135

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}

theorem PretorsionImageClosed.Statement.PretorsionTheory.ext {D : Type*} [Category D] [HasZeroMorphisms D] [HasBinaryBiproducts D]
    {P Q : PretorsionTheory D} (hT : P.T = Q.T) (hF : P.F = Q.F) : P = Q := by sorry
