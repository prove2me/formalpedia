-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_unop_le_unop_iff
-- name    : PretorsionImageClosed.Statement.Subcategory.unop_le_unop_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:25:32.953604+00:00
-- url     : https://prove2.me/theorems/eb107978-7a58-584e-90ee-0be77099c36a
-- title:
--   Subcategory: unop le unop iff
-- statement:
--   The Subcategory construction uses the unop le unop iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L174-L175
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L174-L175

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

theorem PretorsionImageClosed.Statement.Subcategory.unop_le_unop_iff {Z Z' : Subcategory Cᵒᵖ} : Z.unop ≤ Z'.unop ↔ Z ≤ Z' := by sorry
