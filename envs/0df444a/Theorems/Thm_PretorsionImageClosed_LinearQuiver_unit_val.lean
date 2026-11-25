-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_val
-- name    : PretorsionImageClosed.LinearQuiver.unit_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:20:26.724458+00:00
-- url     : https://prove2.me/theorems/989b97c1-b155-4113-bd00-f4403d22ce3b
-- title:
--   Linear Quiver: unit val
-- statement:
--   The Linear Quiver construction uses the unit val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L50-L50
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L50-L50

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

theorem PretorsionImageClosed.LinearQuiver.unit_val (c d i : Fin n) : (unit k c d i : k) = if c ≤ i ∧ i ≤ d then 1 else 0 := by sorry
