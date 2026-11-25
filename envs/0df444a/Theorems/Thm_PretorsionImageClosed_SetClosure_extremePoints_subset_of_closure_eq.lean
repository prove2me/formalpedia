-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_extremePoints_subset_of_closure_eq
-- name    : PretorsionImageClosed.SetClosure.extremePoints_subset_of_closure_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:08:20.791958+00:00
-- url     : https://prove2.me/theorems/8b54c38b-badf-46e4-b937-cc40490d05a0
-- title:
--   Set Closure: extreme Points subset of closure eq
-- statement:
--   Every generating set contains every extreme point.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L84-L94
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Basic.lean#L84-L94

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

theorem PretorsionImageClosed.SetClosure.extremePoints_subset_of_closure_eq
    {B C : Set E} (hBC : c B = C) :
    c.extremePoints C ⊆ B := by sorry
