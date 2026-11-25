-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_coord
-- name    : PretorsionImageClosed.LinearQuiver.coord_eq_coord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:23:51.637084+00:00
-- url     : https://prove2.me/theorems/644c1ff5-ab43-48d2-ac43-e9a6deb2b224
-- title:
--   Linear Quiver: coord eq coord
-- statement:
--   On the overlap `[c, b]`, the coordinates of a morphism agree.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L156-L159
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L156-L159

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

theorem PretorsionImageClosed.LinearQuiver.coord_eq_coord {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (hbd : b ≤ d)
    {i j : Fin n} (hij : i ≤ j) (hi : c ≤ i) (hj : j ≤ b) : coord η j = coord η i := by sorry
