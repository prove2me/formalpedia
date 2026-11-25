-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_bot_mem_quotientsIn_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.bot_mem_quotientsIn_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:29:25.669666+00:00
-- url     : https://prove2.me/theorems/3575deec-31ca-593e-8823-a573e2bfea07
-- title:
--   Subcategory: bot mem quotients In iff
-- statement:
--   The Subcategory construction uses the bot mem quotients In iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L86-L89
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subcategories/Trace.lean#L86-L89

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [Abelian C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (T : Subcategory C) (X : C)
variable (F : Subcategory C)

theorem PretorsionImageClosed.Statement.Subcategory.bot_mem_quotientsIn_iff : ⊥ ∈ F.quotientsIn X ↔ F.prop X := by sorry
