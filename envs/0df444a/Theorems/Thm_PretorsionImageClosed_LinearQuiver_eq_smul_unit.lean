-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_smul_unit
-- name    : PretorsionImageClosed.LinearQuiver.eq_smul_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:02:15.850407+00:00
-- url     : https://prove2.me/theorems/4c925a1b-cea9-54d4-b77a-a3b6f76390de
-- title:
--   Linear Quiver: eq smul unit
-- statement:
--   Every element of a vertex space is a multiple of the unit vector.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L61-L66
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L61-L66

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

theorem PretorsionImageClosed.LinearQuiver.eq_smul_unit {c d i : Fin n} (x : intervalSpace k c d i) : x = (x : k) • unit k c d i := by sorry
