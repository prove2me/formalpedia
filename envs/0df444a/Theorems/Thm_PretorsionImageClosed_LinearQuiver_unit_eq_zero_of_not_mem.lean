-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_eq_zero_of_not_mem
-- name    : PretorsionImageClosed.LinearQuiver.unit_eq_zero_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:03:23.478085+00:00
-- url     : https://prove2.me/theorems/c4eefea9-0502-47b5-ad1f-13da1d394408
-- title:
--   Linear Quiver: unit eq zero of not mem
-- statement:
--   The Linear Quiver construction uses the unit eq zero of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L55-L58
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L55-L58

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

theorem PretorsionImageClosed.LinearQuiver.unit_eq_zero_of_not_mem {c d i : Fin n} (h : ¬ (c ≤ i ∧ i ≤ d)) : unit k c d i = 0 := by sorry
