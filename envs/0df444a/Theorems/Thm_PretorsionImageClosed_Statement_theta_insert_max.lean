-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_theta_insert_max
-- name    : PretorsionImageClosed.Statement.theta_insert_max
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:12:29.452798+00:00
-- url     : https://prove2.me/theorems/4e8b7841-cc96-4fda-864a-f88673c38b12
-- title:
--   Statement: theta insert max
-- statement:
--   The Statement construction uses the theta insert max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L213-L231
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L213-L231

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

theorem PretorsionImageClosed.Statement.theta_insert_max {r : ι} {R : Finset ι} (hr : ∀ x ∈ R, x < r) :
    theta (insert r R) = U * theta R + (X - 1) * X ^ (R.card + 1) := by sorry
