-- Prove2me | Theorems.Thm_ThreeSumApsp_tendsto_ceil_rpow_atTop
-- name    : ThreeSumApsp.tendsto_ceil_rpow_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:13.152948+00:00
-- url     : https://prove2.me/theorems/a488b6eb-aaf1-498b-8bfe-0e9595ab13c1
-- title:
--   Three Sum Apsp: tendsto ceil rpow at Top
-- statement:
--   `⌈n ^ μ⌉` tends to infinity with `n`, for `μ > 0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L43-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L43-L45

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.tendsto_ceil_rpow_atTop {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun n : ℕ => ⌈(n : ℝ) ^ μ⌉₊) atTop atTop := by sorry
