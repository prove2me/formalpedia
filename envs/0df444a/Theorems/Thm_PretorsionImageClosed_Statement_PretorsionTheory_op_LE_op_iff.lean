-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_op_LE_op_iff
-- name    : PretorsionImageClosed.Statement.PretorsionTheory.op_LE_op_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:18:19.961809+00:00
-- url     : https://prove2.me/theorems/89dc87e8-fe54-4605-8f89-549976396251
-- title:
--   Pretorsion Theory: op LE op iff
-- statement:
--   The duality reverses the order (2.2).
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L199-L202
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Duality.lean#L199-L202

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

theorem PretorsionImageClosed.Statement.PretorsionTheory.op_LE_op_iff {P Q : PretorsionTheory C} : P.op.LE Q.op ↔ Q.LE P := by sorry
