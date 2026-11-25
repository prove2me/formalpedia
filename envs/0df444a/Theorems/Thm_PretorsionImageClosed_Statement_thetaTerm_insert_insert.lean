-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_thetaTerm_insert_insert
-- name    : PretorsionImageClosed.Statement.thetaTerm_insert_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:12:21.907229+00:00
-- url     : https://prove2.me/theorems/ee11041a-8d9e-4422-92a4-061b27ef5928
-- title:
--   Statement: theta Term insert insert
-- statement:
--   The Statement construction uses the theta Term insert insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L185-L211
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L185-L211

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

theorem PretorsionImageClosed.Statement.thetaTerm_insert_insert {r : ι} {R J : Finset ι} (hr : ∀ x ∈ R, x < r) (hJ : J ⊆ R) :
    thetaTerm (insert r R) (insert r J) = C q * X * thetaTerm R J := by sorry
