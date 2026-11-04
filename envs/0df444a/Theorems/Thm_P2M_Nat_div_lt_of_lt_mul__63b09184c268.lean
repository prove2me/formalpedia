-- Prove2me | Theorems.Thm_P2M_Nat_div_lt_of_lt_mul__63b09184c268
-- name    : P2M_Nat_div_lt_of_lt_mul__63b09184c268
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:31:48.5113+00:00
-- url     : https://prove2.me/theorems/8c3e27a6-874e-4b17-aec4-36a095ddba63
-- title:
--   P2 M Nat div lt of lt mul  63b09184c268: P2 M Nat div lt of lt mul  63b09184c268
-- statement:
--   The row of an index below `m * n` is below `m`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L57-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Index.lean#L57-L58

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
set_option autoImplicit false
public section
open Nat

theorem P2M_Nat_div_lt_of_lt_mul__63b09184c268 {t m n : ℕ} (h : t < m * n) : t / n < m := by sorry

alias «Nat».«div_lt_of_lt_mul'» := P2M_Nat_div_lt_of_lt_mul__63b09184c268
