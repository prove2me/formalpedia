-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_toInterval_app_apply
-- name    : PretorsionImageClosed.LinearQuiver.toInterval_app_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:01:22.91888+00:00
-- url     : https://prove2.me/theorems/9feaae3c-1bf0-5a7d-a957-a68423b4bc6b
-- title:
--   Linear Quiver: to Interval app apply
-- statement:
--   The Linear Quiver construction uses the to Interval app apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L167-L168
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L167-L168

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

theorem PretorsionImageClosed.LinearQuiver.toInterval_app_apply (hfirst : ∀ i, i < i₀ → IsZero (X.obj i)) (j : Fin n) (x : X.obj j) :
    ((toInterval d ℓ hfirst).app j).hom.hom x = toIntervalLin (i₀ := i₀) d ℓ j x := by sorry
