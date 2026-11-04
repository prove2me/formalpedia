-- Prove2me | Theorems.Thm_ThreeSumApsp_flag_eq_one_iff
-- name    : ThreeSumApsp.flag_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:15.45604+00:00
-- url     : https://prove2.me/theorems/12286a24-b2e6-4634-9c09-63b1859de1c9
-- title:
--   Three Sum Apsp: flag eq one iff
-- statement:
--   The number 1 means yes.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Flag.lean#L32-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Flag.lean#L32-L35

import Mathlib.Algebra.Order.Ring.Int
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
set_option autoImplicit false
section
open ThreeSumApsp

theorem ThreeSumApsp.flag_eq_one_iff {p : Prop} : flag p = 1 ↔ p := by sorry
