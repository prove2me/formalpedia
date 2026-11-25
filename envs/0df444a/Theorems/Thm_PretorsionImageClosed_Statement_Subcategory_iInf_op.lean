-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_iInf_op
-- name    : PretorsionImageClosed.Statement.Subcategory.iInf_op
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:25:57.23671+00:00
-- url     : https://prove2.me/theorems/5a526856-cfa7-42e6-b41d-7d43aaa2b905
-- title:
--   Subcategory: i Inf op
-- statement:
--   The Subcategory construction uses the i Inf op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L177-L182
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L177-L182

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Opposite
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.Statement.Subcategory.iInf_op {ι : Sort*} (Z : ι → Subcategory C) :
    (Subcategory.iInf Z).op = Subcategory.iInf (fun i => (Z i).op) := by sorry
