-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_isZero_interval
-- name    : PretorsionImageClosed.LinearQuiver.not_isZero_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:23:33.745834+00:00
-- url     : https://prove2.me/theorems/495bd0ca-4160-4b80-9f4b-844a94756e24
-- title:
--   Linear Quiver: not is Zero interval
-- statement:
--   The Linear Quiver construction uses the not is Zero interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L189-L195
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Decomposition.lean#L189-L195

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

theorem PretorsionImageClosed.LinearQuiver.not_isZero_interval {a d : Fin n} (h : a ≤ d) : ¬ IsZero (interval k a d) := by sorry
