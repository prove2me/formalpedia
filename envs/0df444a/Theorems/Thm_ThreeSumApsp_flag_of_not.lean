-- Prove2me | Theorems.Thm_ThreeSumApsp_flag_of_not
-- name    : ThreeSumApsp.flag_of_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:30.141114+00:00
-- url     : https://prove2.me/theorems/20f718be-17e0-496e-b506-b9d1b2e55267
-- title:
--   Three Sum Apsp: flag of not
-- statement:
--   The answer no is written as 0.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Flag.lean#L29-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Flag.lean#L29-L29

import Mathlib.Algebra.Order.Ring.Int
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
set_option autoImplicit false
section
open ThreeSumApsp

theorem ThreeSumApsp.flag_of_not {p : Prop} (h : ¬ p) : flag p = 0 := by sorry
