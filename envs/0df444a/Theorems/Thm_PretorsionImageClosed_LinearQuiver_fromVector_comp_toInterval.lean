-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_fromVector_comp_toInterval
-- name    : PretorsionImageClosed.LinearQuiver.fromVector_comp_toInterval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:06:20.328805+00:00
-- url     : https://prove2.me/theorems/ef97f4e0-f287-4b77-93ff-601057850d1b
-- title:
--   Linear Quiver: from Vector comp to Interval
-- statement:
--   `ℓ` with `ℓ(X(i₀ → d)(v)) = 1` makes `toInterval` a retraction of `fromVector`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L171-L183
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L171-L183

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
variable (X : Statement.LinRep k n) (i₀ : Fin n) (v : X.obj i₀)
variable {X i₀ v} (d : Fin n)
variable (ℓ : Module.Dual k (X.obj d))

theorem PretorsionImageClosed.LinearQuiver.fromVector_comp_toInterval (hd : ∀ j, d < j → vmap X i₀ v j = 0)
    (hfirst : ∀ i, i < i₀ → IsZero (X.obj i)) (hℓ : ℓ (vmap X i₀ v d) = 1) :
    fromVector d hd ≫ toInterval d ℓ hfirst = 𝟙 _ := by sorry
