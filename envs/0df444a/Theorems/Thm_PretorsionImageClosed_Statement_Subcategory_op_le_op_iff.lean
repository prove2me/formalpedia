-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_op_le_op_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.op_le_op_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:18:05.229724+00:00
-- url     : https://prove2.me/theorems/d6b70e71-e02f-4114-ba98-6d89c973c7f8
-- title:
--   Subcategory: op le op iff
-- statement:
--   The Subcategory construction uses the op le op iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L171-L172
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L171-L172

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Opposite
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.Statement.Subcategory.op_le_op_iff {Z Z' : Subcategory C} : Z.op ≤ Z'.op ↔ Z ≤ Z' := by sorry
