-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
-- name    : PretorsionImageClosed.Statement.IsPretorsionTheory.isSubobjectClosed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:42:10.481332+00:00
-- url     : https://prove2.me/theorems/2284d93e-4051-4687-8112-0e070fa6337c
-- title:
--   Is Pretorsion Theory: is Subobject Closed
-- statement:
--   Proposition 2.3 (Campanini–Fedele–Yıldırım), second half: the second
--   component of a pretorsion theory is subobject-closed.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L112-L123
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L112-L123

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

theorem PretorsionImageClosed.Statement.IsPretorsionTheory.isSubobjectClosed {T F : Subcategory C}
    (h : IsPretorsionTheory T.prop F.prop) : F.IsSubobjectClosed := by sorry
