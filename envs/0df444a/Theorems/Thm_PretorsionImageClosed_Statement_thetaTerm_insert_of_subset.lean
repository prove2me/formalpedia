-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_thetaTerm_insert_of_subset
-- name    : PretorsionImageClosed.Statement.thetaTerm_insert_of_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:11:58.15239+00:00
-- url     : https://prove2.me/theorems/99a4e7f4-19e0-5059-911a-3bc0e098216d
-- title:
--   Statement: theta Term insert of subset
-- statement:
--   The Statement construction uses the theta Term insert of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L171-L183
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L171-L183

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

theorem PretorsionImageClosed.Statement.thetaTerm_insert_of_subset {r : ι} {R J : Finset ι} (hr : ∀ x ∈ R, x < r) (hJ : J ⊆ R) :
    thetaTerm (insert r R) J = thetaTerm R J * (if J = ∅ then X else 1) := by sorry
