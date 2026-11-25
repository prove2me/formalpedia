-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_psiTerm_insert_insert
-- name    : PretorsionImageClosed.Statement.psiTerm_insert_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:11:36.174145+00:00
-- url     : https://prove2.me/theorems/0552142b-91e8-46a2-8058-34c33b2210fd
-- title:
--   Statement: psi Term insert insert
-- statement:
--   The Statement construction uses the psi Term insert insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L61-L131
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L61-L131

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

theorem PretorsionImageClosed.Statement.psiTerm_insert_insert {r : ι} {R Cont : Finset ι} (hr : ∀ x ∈ R, x < r)
    (hCont : Cont ⊆ R) :
    psiTerm (insert r R) (insert r Cont) =
      X * (C q * psiTerm R Cont + if Cont = R then X ^ R.card else 0) := by sorry
