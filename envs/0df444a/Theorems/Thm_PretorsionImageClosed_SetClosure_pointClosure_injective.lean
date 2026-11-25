-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_injective
-- name    : PretorsionImageClosed.SetClosure.pointClosure_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:13:13.613238+00:00
-- url     : https://prove2.me/theorems/19fa9ac9-645c-415c-9867-54696e40adb2
-- title:
--   Set Closure: point Closure injective
-- statement:
--   Distinct points have distinct point closures in a convex geometry.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L167-L181
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L167-L181

module
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Order.Closure
public import Mathlib.Order.Preorder.Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed
open PretorsionImageClosed.SetClosure
variable {E : Type*} (c : SetClosure E)
variable {c}

theorem PretorsionImageClosed.SetClosure.pointClosure_injective
    (hae : c.IsAntiExchange) (hempty : c.IsClosed ∅) :
    Function.Injective (fun x : E ↦ c ({x} : Set E)) := by sorry
