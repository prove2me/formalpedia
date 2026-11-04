-- Prove2me | Theorems.Thm_ThreeSumApsp_flag_mem
-- name    : ThreeSumApsp.flag_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:22.392657+00:00
-- url     : https://prove2.me/theorems/ec912906-e494-449e-927f-b0df85bd6f3e
-- title:
--   Three Sum Apsp: flag mem
-- statement:
--   An answer is 0 or 1.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Flag.lean#L42-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Flag.lean#L42-L45

import Mathlib.Algebra.Order.Ring.Int
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
set_option autoImplicit false
section
open ThreeSumApsp

theorem ThreeSumApsp.flag_mem (p : Prop) : 0 ≤ flag p ∧ flag p < 2 := by sorry
