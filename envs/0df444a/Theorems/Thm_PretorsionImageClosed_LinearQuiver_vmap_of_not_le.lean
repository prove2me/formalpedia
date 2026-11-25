-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_vmap_of_not_le
-- name    : PretorsionImageClosed.LinearQuiver.vmap_of_not_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:00:14.29617+00:00
-- url     : https://prove2.me/theorems/94bfba03-f31c-5cf5-819c-b8fa0176c03a
-- title:
--   Linear Quiver: vmap of not le
-- statement:
--   The Linear Quiver construction uses the vmap of not le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L59-L61
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L59-L61

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

theorem PretorsionImageClosed.LinearQuiver.vmap_of_not_le {j : Fin n} (h : ¬ i₀ ≤ j) : vmap X i₀ v j = 0 := by sorry
