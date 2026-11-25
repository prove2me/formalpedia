-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_isClosed_pointClosure_sdiff_singleton
-- name    : PretorsionImageClosed.SetClosure.isClosed_pointClosure_sdiff_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:12:40.822494+00:00
-- url     : https://prove2.me/theorems/54e37592-1b9b-4315-a195-841b9425097a
-- title:
--   Set Closure: is Closed point Closure sdiff singleton
-- statement:
--   In a finitary anti-exchange closure with closed empty set, deleting
--   the generating point from its point closure leaves a closed set.
--
--   This is the key step behind complete join-irreducibility of point
--   closures in the equidistribution paper.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L102-L164
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L102-L164

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

theorem PretorsionImageClosed.SetClosure.isClosed_pointClosure_sdiff_singleton
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) (x : E) :
    c.IsClosed (c ({x} : Set E) \ {x}) := by sorry
