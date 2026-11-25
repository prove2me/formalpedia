-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_psiTerm_insert_of_subset
-- name    : PretorsionImageClosed.Statement.psiTerm_insert_of_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:11:13.605439+00:00
-- url     : https://prove2.me/theorems/d33fda2f-33f0-407d-8650-86a881dab517
-- title:
--   Statement: psi Term insert of subset
-- statement:
--   The Statement construction uses the psi Term insert of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L47-L59
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean#L47-L59

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

theorem PretorsionImageClosed.Statement.psiTerm_insert_of_subset {r : ι} {R Cont : Finset ι} (hr : ∀ x ∈ R, x < r)
    (hCont : Cont ⊆ R) : psiTerm (insert r R) Cont = psiTerm R Cont := by sorry
