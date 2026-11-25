-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_U_sub_X_ne_zero
-- name    : PretorsionImageClosed.Statement.U_sub_X_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:09:17.19513+00:00
-- url     : https://prove2.me/theorems/45da0aeb-03d5-54b2-bc4c-4190e7398069
-- title:
--   Statement: U sub X ne zero
-- statement:
--   The Statement construction uses the U sub X ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean#L67-L70
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/Delta.lean#L67-L70

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial

theorem PretorsionImageClosed.Statement.U_sub_X_ne_zero : (U - X : Rq[X]) ≠ 0 := by sorry
