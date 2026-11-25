-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_iso_biprod_interval
-- name    : PretorsionImageClosed.LinearQuiver.exists_iso_biprod_interval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:26:28.081797+00:00
-- url     : https://prove2.me/theorems/ae2b7538-843c-4e9c-81b9-5f8a1ff26591
-- title:
--   Linear Quiver: exists iso biprod interval
-- statement:
--   Splitting off the interval through a vector at the first nonzero vertex.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L213-L260
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L213-L260

module
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.exists_iso_biprod_interval (X : Statement.LinRep k n) (hX : ¬ IsZero X) :
    ∃ (a d : Fin n) (_ : a ≤ d) (X' : Statement.LinRep k n),
      Nonempty (X ≅ interval k a d ⊞ X') := by sorry
