-- Prove2me | Theorems.Thm_ThreeSumApsp_rpow_mul_rpow_eventuallyEq
-- name    : ThreeSumApsp.rpow_mul_rpow_eventuallyEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:18.476222+00:00
-- url     : https://prove2.me/theorems/0066824c-4c93-478f-b5ca-d52a77fa16cc
-- title:
--   Three Sum Apsp: rpow mul rpow eventually Eq
-- statement:
--   `n ^ a * n ^ b = n ^ (a + b)` for all large `n`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L55-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L55-L58

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.rpow_mul_rpow_eventuallyEq (a b : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ b) =ᶠ[atTop] fun n : ℕ => (n : ℝ) ^ (a + b) := by sorry
