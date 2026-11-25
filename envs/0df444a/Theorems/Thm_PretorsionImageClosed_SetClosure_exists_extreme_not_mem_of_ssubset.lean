-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_exists_extreme_not_mem_of_ssubset
-- name    : PretorsionImageClosed.SetClosure.exists_extreme_not_mem_of_ssubset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:15:00.290054+00:00
-- url     : https://prove2.me/theorems/4bd67cea-6ef0-4b1c-848b-9a3e842f75de
-- title:
--   Set Closure: exists extreme not mem of ssubset
-- statement:
--   A proper inclusion of finite closed sets admits a legal one-point
--   deletion of the upper set which stays above the lower set.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L205-L219
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L205-L219

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}

theorem PretorsionImageClosed.SetClosure.exists_extreme_not_mem_of_ssubset [Finite E]
    (hae : c.IsAntiExchange) {C D : Set E}
    (hC : c.IsClosed C) (hD : c.IsClosed D) (hCD : C ⊂ D) :
    ∃ x ∈ c.extremePoints D, x ∉ C := by sorry
