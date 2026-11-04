-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerScan_stageValue_below
-- name    : ThreeSum.LightTernaryEulerScan.stageValue_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:49.366623+00:00
-- url     : https://prove2.me/theorems/ae8390b2-eb42-4ac4-bfea-2bc54ba68a39
-- title:
--   Light Ternary Euler Scan: stage Value below
-- statement:
--   The Light Ternary Euler Scan construction uses the stage Value below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerScan.lean#L25-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerScan.lean#L25-L28

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerScan
open Light
set_option maxHeartbeats 1800000

theorem ThreeSum.LightTernaryEulerScan.stageValue_below (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    {vals current j a : ℕ} (ha : a < vals) :
    stageValue μ f rank vals current j a=μ a := by sorry
