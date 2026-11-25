-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
-- name    : PretorsionImageClosed.Statement.IsPretorsionTheory.isQuotientClosed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:41:42.419427+00:00
-- url     : https://prove2.me/theorems/cbbd1697-65dd-4cd7-89db-894143e16b9b
-- title:
--   Is Pretorsion Theory: is Quotient Closed
-- statement:
--   Proposition 2.3 (Campanini–Fedele–Yıldırım), first half: the first
--   component of a pretorsion theory is quotient-closed.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L97-L108
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L97-L108

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
variable [HasZeroMorphisms C] [HasBinaryBiproducts C] [Balanced C]

theorem PretorsionImageClosed.Statement.IsPretorsionTheory.isQuotientClosed {T F : Subcategory C}
    (h : IsPretorsionTheory T.prop F.prop) : T.IsQuotientClosed := by sorry
