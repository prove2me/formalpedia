-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_vmap_self
-- name    : PretorsionImageClosed.LinearQuiver.vmap_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:04:45.817621+00:00
-- url     : https://prove2.me/theorems/7ecf3d3b-5ebf-5f06-a934-b45a1cb2eaee
-- title:
--   Linear Quiver: vmap self
-- statement:
--   The Linear Quiver construction uses the vmap self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L63-L67
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L63-L67

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

theorem PretorsionImageClosed.LinearQuiver.vmap_self : vmap X i₀ v i₀ = v := by sorry
