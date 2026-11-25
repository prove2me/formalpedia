-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_psi_empty
-- name    : PretorsionImageClosed.Statement.psi_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:12:51.186354+00:00
-- url     : https://prove2.me/theorems/092c2c13-09e1-4c0f-ae7c-0b8e6100145f
-- title:
--   Statement: psi empty
-- statement:
--   The Statement construction uses the psi empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L44-L45
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L44-L45

module
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial Finset
variable {ι : Type*} [LinearOrder ι]

theorem PretorsionImageClosed.Statement.psi_empty : psi (∅ : Finset ι) = 1 := by sorry
