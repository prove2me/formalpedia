-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigO_rpow_rpow_of_le
-- name    : ThreeSumApsp.isBigO_rpow_rpow_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:03.327766+00:00
-- url     : https://prove2.me/theorems/e1891df8-5647-46ed-b510-f539635c1dcf
-- title:
--   Three Sum Apsp: is Big O rpow rpow of le
-- statement:
--   `n ^ a = O(n ^ b)` for `a ≤ b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L48-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L48-L52

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.isBigO_rpow_rpow_of_le {a b : ℝ} (hab : a ≤ b) :
    (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] fun n : ℕ => (n : ℝ) ^ b := by sorry
