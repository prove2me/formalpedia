-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_intervalIncl
-- name    : PretorsionImageClosed.LinearQuiver.coord_intervalIncl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:08:26.781891+00:00
-- url     : https://prove2.me/theorems/22ca3f09-a216-4bb8-9053-e5b0260821e1
-- title:
--   Linear Quiver: coord interval Incl
-- statement:
--   The Linear Quiver construction uses the coord interval Incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L91-L96
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L91-L96

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.coord_intervalIncl {a ℓ d : Fin n} (h : a ≤ ℓ) (i : Fin n) :
    coord (intervalIncl k d h) i = if ℓ ≤ i ∧ i ≤ d then 1 else 0 := by sorry
