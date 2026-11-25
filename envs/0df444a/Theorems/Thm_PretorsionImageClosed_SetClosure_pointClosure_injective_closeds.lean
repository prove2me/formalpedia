-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_injective_closeds
-- name    : PretorsionImageClosed.SetClosure.pointClosure_injective_closeds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:27:15.898606+00:00
-- url     : https://prove2.me/theorems/2006f1c1-55ea-5b17-af08-e1ec1be550bf
-- title:
--   Set Closure: point Closure injective closeds
-- statement:
--   Distinct ground points give distinct point closures, now as elements
--   of the closed-set lattice.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L86-L91
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L86-L91

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

theorem PretorsionImageClosed.SetClosure.pointClosure_injective_closeds
    (hae : c.IsAntiExchange) (hempty : c.IsClosed ∅) :
    Function.Injective c.pointClosure := by sorry
