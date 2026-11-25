-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_not_mem_src
-- name    : PretorsionImageClosed.LinearQuiver.coord_eq_zero_of_not_mem_src
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:46.530446+00:00
-- url     : https://prove2.me/theorems/8b2b99ba-9814-4a3c-9549-2c8549a84bc8
-- title:
--   Linear Quiver: coord eq zero of not mem src
-- statement:
--   The Linear Quiver construction uses the coord eq zero of not mem src property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L84-L89
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L84-L89

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable (k : Type u) [Field k] {n : ℕ}
variable {k}

theorem PretorsionImageClosed.LinearQuiver.coord_eq_zero_of_not_mem_src {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    {i : Fin n} (h : ¬ (c ≤ i ∧ i ≤ d)) : coord η i = 0 := by sorry
