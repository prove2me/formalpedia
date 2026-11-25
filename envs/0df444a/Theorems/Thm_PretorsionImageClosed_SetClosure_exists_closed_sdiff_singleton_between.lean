-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_exists_closed_sdiff_singleton_between
-- name    : PretorsionImageClosed.SetClosure.exists_closed_sdiff_singleton_between
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:15:16.13841+00:00
-- url     : https://prove2.me/theorems/c7247fb5-f24c-4dab-b405-e6e225d972d5
-- title:
--   Set Closure: exists closed sdiff singleton between
-- statement:
--   Accessibility in interval form: a proper inclusion of finite closed
--   sets can be shortened by deleting one extreme point from the upper set.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L223-L233
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L223-L233

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

theorem PretorsionImageClosed.SetClosure.exists_closed_sdiff_singleton_between [Finite E]
    (hae : c.IsAntiExchange) {C D : Set E}
    (hC : c.IsClosed C) (hD : c.IsClosed D) (hCD : C ⊂ D) :
    ∃ x : E, x ∈ D \ C ∧ c.IsClosed (D \ {x}) ∧ C ⊆ D \ {x} := by sorry
