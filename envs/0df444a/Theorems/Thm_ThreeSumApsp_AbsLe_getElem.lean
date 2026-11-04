-- Prove2me | Theorems.Thm_ThreeSumApsp_AbsLe_getElem
-- name    : ThreeSumApsp.AbsLe.getElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:37.653468+00:00
-- url     : https://prove2.me/theorems/c040d280-23ae-4a1e-8762-1a3e0ca84148
-- title:
--   Abs Le: get Elem
-- statement:
--   A bound on the absolute values of all members bounds every entry.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L439-L441
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L439-L441

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

theorem ThreeSumApsp.AbsLe.getElem {l : List ℤ} {U : ℤ} (h : AbsLe l U) {i : ℕ} (hi : i < l.length) :
    |l[i]| ≤ U := by sorry
