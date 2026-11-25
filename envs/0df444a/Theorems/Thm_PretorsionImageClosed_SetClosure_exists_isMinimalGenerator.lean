-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_exists_isMinimalGenerator
-- name    : PretorsionImageClosed.SetClosure.exists_isMinimalGenerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:29:36.916265+00:00
-- url     : https://prove2.me/theorems/5bba9627-c57f-57a8-987f-9b4acde3a037
-- title:
--   Set Closure: exists is Minimal Generator
-- statement:
--   Every closed set on a finite ground type has an inclusion-minimal
--   generating set.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L119-L134
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L119-L134

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

theorem PretorsionImageClosed.SetClosure.exists_isMinimalGenerator [Finite E]
    {C : Set E} (hC : c.IsClosed C) :
    ∃ B : Set E, c.IsMinimalGenerator B C := by sorry
