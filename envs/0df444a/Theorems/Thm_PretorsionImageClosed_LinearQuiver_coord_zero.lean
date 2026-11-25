-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_zero
-- name    : PretorsionImageClosed.LinearQuiver.coord_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:29:25.523025+00:00
-- url     : https://prove2.me/theorems/d066218b-2b08-499e-8f11-898c528f32f8
-- title:
--   Linear Quiver: coord zero
-- statement:
--   The Linear Quiver construction uses the coord zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L53-L56
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L53-L56

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
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

theorem PretorsionImageClosed.LinearQuiver.coord_zero (c d a b i : Fin n) : coord (0 : interval k c d ⟶ interval k a b) i = 0 := by sorry
