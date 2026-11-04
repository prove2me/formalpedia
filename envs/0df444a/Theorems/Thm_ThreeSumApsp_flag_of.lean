-- Prove2me | Theorems.Thm_ThreeSumApsp_flag_of
-- name    : ThreeSumApsp.flag_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:29.250877+00:00
-- url     : https://prove2.me/theorems/de515402-14a4-4371-b930-a7e5f9cf3a7a
-- title:
--   Three Sum Apsp: flag of
-- statement:
--   The answer yes is written as 1.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Flag.lean#L26-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Flag.lean#L26-L26

import Mathlib.Algebra.Order.Ring.Int
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
set_option autoImplicit false
section
open ThreeSumApsp

theorem ThreeSumApsp.flag_of {p : Prop} (h : p) : flag p = 1 := by sorry
