-- Prove2me | Theorems.Thm_ThreeSumApsp_eventually_mul_rpow_le
-- name    : ThreeSumApsp.eventually_mul_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:22.779171+00:00
-- url     : https://prove2.me/theorems/30aacf05-8680-4714-9cba-f4c354836ed4
-- title:
--   Three Sum Apsp: eventually mul rpow le
-- statement:
--   `C * n ^ a ≤ n ^ b` for all large `n`, if `a < b`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L106-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L106-L108

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.eventually_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by sorry
