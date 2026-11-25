-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf
-- name    : PretorsionImageClosed.Statement.Subcategory.IsImageClosed.iInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:52.761167+00:00
-- url     : https://prove2.me/theorems/522f0c5c-f557-4234-afee-bc95d9c24419
-- title:
--   Is Image Closed: i Inf
-- statement:
--   The Is Image Closed construction uses the i Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L256-L260
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Basic.lean#L256-L260

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
variable {A : Type*} [Category A] [Abelian A]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory A)

theorem PretorsionImageClosed.Statement.Subcategory.IsImageClosed.iInf {ι : Sort*} {Z : ι → Subcategory A} (h : ∀ i, (Z i).IsImageClosed) :
    (Subcategory.iInf Z).IsImageClosed := by sorry
