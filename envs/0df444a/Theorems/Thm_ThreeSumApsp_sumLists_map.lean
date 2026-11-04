-- Prove2me | Theorems.Thm_ThreeSumApsp_sumLists_map
-- name    : ThreeSumApsp.sumLists_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:40.774374+00:00
-- url     : https://prove2.me/theorems/66101809-5094-426b-9336-d9f6f6329375
-- title:
--   Three Sum Apsp: sum Lists map
-- statement:
--   The entrywise sum of lists that are images of one list.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L460-L474
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L460-L474

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
set_option autoImplicit false
public section
open ThreeSumApsp
variable {α β : Type*}

theorem ThreeSumApsp.sumLists_map (l : List α) (ts : List β) (f : β → α → ℤ) :
    sumLists l.length (ts.map fun t => l.map (f t)) =
      l.map fun c => (ts.map fun t => f t c).sum := by sorry
