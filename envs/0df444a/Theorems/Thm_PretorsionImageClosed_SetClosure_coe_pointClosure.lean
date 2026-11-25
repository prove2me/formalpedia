-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_coe_pointClosure
-- name    : PretorsionImageClosed.SetClosure.coe_pointClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:49:34.986127+00:00
-- url     : https://prove2.me/theorems/a68658eb-e363-4a1f-a6a2-79d31d2c57db
-- title:
--   Set Closure: coe point Closure
-- statement:
--   The Set Closure construction uses the coe point Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L37-L39
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L37-L39

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

theorem PretorsionImageClosed.SetClosure.coe_pointClosure (c : SetClosure E) (x : E) :
    (c.pointClosure x : Set E) = c ({x} : Set E) := by sorry

attribute [defeq] PretorsionImageClosed.SetClosure.coe_pointClosure
