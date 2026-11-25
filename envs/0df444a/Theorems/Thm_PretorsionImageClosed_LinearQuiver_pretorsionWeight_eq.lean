-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_pretorsionWeight_eq
-- name    : PretorsionImageClosed.LinearQuiver.pretorsionWeight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:32:25.492886+00:00
-- url     : https://prove2.me/theorems/9d04b641-cbe1-4935-b27d-c7b4b0e43f6f
-- title:
--   Linear Quiver: pretorsion Weight eq
-- statement:
--   The weight of a pretorsion theory is the weight of its cutoff pair.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffWeights.lean#L84-L90
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffWeights.lean#L84-L90

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffCriterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.pretorsionWeight_eq (P : PretorsionTheory (Statement.LinRep k n)) :
    pretorsionWeight k n P = cpWeight (pretorsionEquiv P) := by sorry
