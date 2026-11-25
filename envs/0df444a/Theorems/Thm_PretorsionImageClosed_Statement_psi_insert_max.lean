-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_psi_insert_max
-- name    : PretorsionImageClosed.Statement.psi_insert_max
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:11:34.892794+00:00
-- url     : https://prove2.me/theorems/90e99b30-ffbe-420e-8c79-d24c5d14070d
-- title:
--   Statement: psi insert max
-- statement:
--   The Statement construction uses the psi insert max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L133-L144
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L133-L144

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

theorem PretorsionImageClosed.Statement.psi_insert_max {r : ι} {R : Finset ι} (hr : ∀ x ∈ R, x < r) :
    psi (insert r R) = U * psi R + X ^ (R.card + 1) := by sorry
