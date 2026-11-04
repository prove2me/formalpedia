-- Prove2me | Theorems.Thm_P2M_Light_getElem__append_length_add_3291fe153891
-- name    : P2M_Light_getElem__append_length_add_3291fe153891
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:33.478174+00:00
-- url     : https://prove2.me/theorems/a526698c-9f9b-4e8f-800e-f77f0af997e7
-- title:
--   P2 M Light get Elem  append length add 3291fe153891: P2 M Light get Elem  append length add 3291fe153891
-- statement:
--   Procedure number i of a list that is appended to the program P₀ has the number |P₀| + i.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L56-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L56-L59

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

theorem P2M_Light_getElem__append_length_add_3291fe153891 (P₀ : Program) {R : Program} {i : ℕ} {body : Stmt}
    (h : R[i]? = some body) : (P₀ ++ R)[P₀.length + i]? = some body := by sorry

alias «Light».«getElem?_append_length_add» := P2M_Light_getElem__append_length_add_3291fe153891
