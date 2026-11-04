-- Prove2me | Theorems.Thm_P2M_Light_getElem__append_append_bf65dc55a47e
-- name    : P2M_Light_getElem__append_append_bf65dc55a47e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:32.564327+00:00
-- url     : https://prove2.me/theorems/1ab227f4-a04f-4125-8068-a7fc3e83ece7
-- title:
--   P2 M Light get Elem  append append bf65dc55a47e: P2 M Light get Elem  append append bf65dc55a47e
-- statement:
--   Procedure number i of a list that is appended to the program P₀ has the number |P₀| + i,
--   whatever is appended after the list.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L50-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L50-L53

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
public import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem P2M_Light_getElem__append_append_bf65dc55a47e {P₀ B : Program} (R : Program) {i : ℕ} {body : Stmt}
    (h : B[i]? = some body) : (P₀ ++ (B ++ R))[P₀.length + i]? = some body := by sorry

alias «Light».«getElem?_append_append» := P2M_Light_getElem__append_append_bf65dc55a47e
