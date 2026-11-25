-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_hom_ext_coord
-- name    : PretorsionImageClosed.LinearQuiver.hom_ext_coord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:20:31.463715+00:00
-- url     : https://prove2.me/theorems/367abccd-6f7d-4a52-a0b5-7bf5fbbe3293
-- title:
--   Linear Quiver: hom ext coord
-- statement:
--   Two morphisms between interval representations with the same coordinates
--   are equal.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L97-L104
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L97-L104

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

theorem PretorsionImageClosed.LinearQuiver.hom_ext_coord {c d a b : Fin n} {η η' : interval k c d ⟶ interval k a b}
    (h : ∀ i, coord η i = coord η' i) : η = η' := by sorry
