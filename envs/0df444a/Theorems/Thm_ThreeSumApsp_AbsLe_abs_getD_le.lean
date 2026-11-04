-- Prove2me | Theorems.Thm_ThreeSumApsp_AbsLe_abs_getD_le
-- name    : ThreeSumApsp.AbsLe.abs_getD_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:39.668204+00:00
-- url     : https://prove2.me/theorems/42aa157e-2998-4de5-b868-8700bba79c49
-- title:
--   Abs Le: abs get D le
-- statement:
--   A bound on the absolute values of all members bounds every `getD` with default `0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L449-L451
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L449-L451

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

theorem ThreeSumApsp.AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U := by sorry
