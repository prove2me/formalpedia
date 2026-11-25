-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_coord_mul_canonical
-- name    : PretorsionImageClosed.LinearQuiver.coord_eq_coord_mul_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:25:13.583469+00:00
-- url     : https://prove2.me/theorems/6dc07f8e-6770-4f65-904b-a19e7decbf6f
-- title:
--   Linear Quiver: coord eq coord mul canonical
-- statement:
--   Proposition 5.2: for `a ≤ c` and `b ≤ d`, every morphism `M_{c,d} ⟶ M_{a,b}`
--   is the scalar `coord η c` times the canonical morphism, in coordinates.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L213-L223
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Hom.lean#L213-L223

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

theorem PretorsionImageClosed.LinearQuiver.coord_eq_coord_mul_canonical {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    (hac : a ≤ c) (hbd : b ≤ d) (i : Fin n) :
    coord η i = coord η c * coord (canonicalHom (k := k) hac hbd) i := by sorry
