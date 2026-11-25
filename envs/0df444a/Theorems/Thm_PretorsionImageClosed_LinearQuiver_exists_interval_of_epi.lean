-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_interval_of_epi
-- name    : PretorsionImageClosed.LinearQuiver.exists_interval_of_epi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:11:17.11986+00:00
-- url     : https://prove2.me/theorems/1a17f993-18ba-4b3d-b38d-1e27ec31053a
-- title:
--   Linear Quiver: exists interval of epi
-- statement:
--   An interval quotient of an object of `C` is a quotient of an interval of `C`
--   with the same left endpoint and a larger right endpoint.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L70-L92
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L70-L92

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.exists_interval_of_epi (C : Subcategory (Statement.LinRep k n)) {a b : Fin n} (hab : a ≤ b)
    {X : Statement.LinRep k n} (hX : C.prop X) (p : X ⟶ interval k a b) [Epi p] :
    ∃ d : Fin n, b ≤ d ∧ C.prop (interval k a d) := by sorry
