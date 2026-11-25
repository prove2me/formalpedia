-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_not_mem_tgt
-- name    : PretorsionImageClosed.LinearQuiver.coord_eq_zero_of_not_mem_tgt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:49.577423+00:00
-- url     : https://prove2.me/theorems/6fa7d45f-1350-42f1-8695-52eb72611def
-- title:
--   Linear Quiver: coord eq zero of not mem tgt
-- statement:
--   The Linear Quiver construction uses the coord eq zero of not mem tgt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L91-L93
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L91-L93

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

theorem PretorsionImageClosed.LinearQuiver.coord_eq_zero_of_not_mem_tgt {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    {i : Fin n} (h : ¬ (a ≤ i ∧ i ≤ b)) : coord η i = 0 := by sorry
