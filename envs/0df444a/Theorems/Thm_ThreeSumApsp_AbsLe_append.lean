-- Prove2me | Theorems.Thm_ThreeSumApsp_AbsLe_append
-- name    : ThreeSumApsp.AbsLe.append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:32:38.972011+00:00
-- url     : https://prove2.me/theorems/db368deb-6cba-4577-97af-a6fb02838951
-- title:
--   Abs Le: append
-- statement:
--   Two lists with a common bound, one after the other.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L444-L446
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/List.lean#L444-L446

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

theorem ThreeSumApsp.AbsLe.append {l₁ l₂ : List ℤ} {U : ℤ} (h₁ : AbsLe l₁ U) (h₂ : AbsLe l₂ U) :
    AbsLe (l₁ ++ l₂) U := by sorry
