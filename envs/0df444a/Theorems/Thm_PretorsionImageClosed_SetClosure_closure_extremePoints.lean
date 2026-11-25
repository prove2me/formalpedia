-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_closure_extremePoints
-- name    : PretorsionImageClosed.SetClosure.closure_extremePoints
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:32:57.3429+00:00
-- url     : https://prove2.me/theorems/643c1a68-a4ed-4385-84b3-543c80a6df01
-- title:
--   Set Closure: closure extreme Points
-- statement:
--   The extreme points form the unique minimal generating set of a closed
--   set in a finite anti-exchange closure system.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L184-L189
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L184-L189

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

theorem PretorsionImageClosed.SetClosure.closure_extremePoints [Finite E]
    (hae : c.IsAntiExchange) {C : Set E} (hC : c.IsClosed C) :
    c (c.extremePoints C) = C := by sorry
