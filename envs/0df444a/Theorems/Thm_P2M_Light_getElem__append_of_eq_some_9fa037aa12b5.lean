-- Prove2me | Theorems.Thm_P2M_Light_getElem__append_of_eq_some_9fa037aa12b5
-- name    : P2M_Light_getElem__append_of_eq_some_9fa037aa12b5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:31.711196+00:00
-- url     : https://prove2.me/theorems/17f787cd-43f0-4da4-a642-9b08816e7a6e
-- title:
--   P2 M Light get Elem  append of eq some 9fa037aa12b5: P2 M Light get Elem  append of eq some 9fa037aa12b5
-- statement:
--   A procedure of a program is a procedure, with the same number, of the program with more
--   procedures appended.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L43-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L43-L46

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

theorem P2M_Light_getElem__append_of_eq_some_9fa037aa12b5 {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by sorry

alias «Light».«getElem?_append_of_eq_some» := P2M_Light_getElem__append_of_eq_some_9fa037aa12b5
