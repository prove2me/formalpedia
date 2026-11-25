-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_iSup_pointClosure
-- name    : PretorsionImageClosed.SetClosure.iSup_pointClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:56:57.677593+00:00
-- url     : https://prove2.me/theorems/755647ba-6585-4781-b00a-5f4c95af3acb
-- title:
--   Set Closure: i Sup point Closure
-- statement:
--   Every closed set is the supremum of the point closures of its
--   elements.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L95-L106
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L95-L106

module
public import Mathlib.Order.Grade
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*}
variable {c : SetClosure E}

theorem PretorsionImageClosed.SetClosure.iSup_pointClosure (C : c.Closeds) :
    (⨆ x : (C : Set E), c.pointClosure x.1) = C := by sorry
