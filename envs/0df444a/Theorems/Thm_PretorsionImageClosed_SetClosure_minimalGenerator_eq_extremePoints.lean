-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_minimalGenerator_eq_extremePoints
-- name    : PretorsionImageClosed.SetClosure.minimalGenerator_eq_extremePoints
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:15:29.451437+00:00
-- url     : https://prove2.me/theorems/617603bf-c1e8-4400-b663-7874ddc39f38
-- title:
--   Set Closure: minimal Generator eq extreme Points
-- statement:
--   A one-point-minimal generator is the set of extreme points.  This is
--   the finite anti-exchange core of uniqueness of minimal generators.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L138-L180
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L138-L180

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

theorem PretorsionImageClosed.SetClosure.minimalGenerator_eq_extremePoints [Finite E]
    (hae : c.IsAntiExchange) {B C : Set E}
    (hC : c.IsClosed C) (hB : c.IsMinimalGenerator B C) :
    B = c.extremePoints C := by sorry
