-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_fromVector_app_apply
-- name    : PretorsionImageClosed.LinearQuiver.fromVector_app_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:01:06.97699+00:00
-- url     : https://prove2.me/theorems/3be23e71-7a7c-5479-9655-89d1cccb2a2e
-- title:
--   Linear Quiver: from Vector app apply
-- statement:
--   The Linear Quiver construction uses the from Vector app apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L108-L110
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L108-L110

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

theorem PretorsionImageClosed.LinearQuiver.fromVector_app_apply (hd : ∀ j, d < j → vmap X i₀ v j = 0) (j : Fin n)
    (x : intervalSpace k i₀ d j) :
    ((fromVector d hd).app j).hom.hom x = (x : k) • vmap X i₀ v j := by sorry
