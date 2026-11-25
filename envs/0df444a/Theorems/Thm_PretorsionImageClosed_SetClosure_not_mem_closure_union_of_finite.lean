-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_not_mem_closure_union_of_finite
-- name    : PretorsionImageClosed.SetClosure.not_mem_closure_union_of_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:32:29.630994+00:00
-- url     : https://prove2.me/theorems/1c4af5c4-0d84-4921-bf1c-4546d3bef5c9
-- title:
--   Set Closure: not mem closure union of finite
-- statement:
--   Anti-exchange can be iterated over a finite set: if all points of `Y`
--   are available after adding `b` to a closed set `K`, then adjoining all of
--   `Y` without `b` still cannot regenerate `b`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L62-L115
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L62-L115

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

theorem PretorsionImageClosed.SetClosure.not_mem_closure_union_of_finite
    (hae : c.IsAntiExchange) {K Y : Set E} {b : E}
    (hK : c.IsClosed K) (hbK : b ∉ K) (hYfin : Y.Finite)
    (hY : Y ⊆ c (insert b K)) (hbY : b ∉ Y) :
    b ∉ c (K ∪ Y) := by sorry
