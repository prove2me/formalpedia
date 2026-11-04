-- Prove2me | Theorems.Thm_ThreeSum_TrimScales_replicatedHalf_log_rate_w3sum_ac885d1
-- name    : ThreeSum.TrimScales.replicatedHalf_log_rate_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:13.315734+00:00
-- url     : https://prove2.me/theorems/d7baf466-3a83-48d6-895a-bbff1b8d0881
-- title:
--   Trim Scales: replicated Half log rate
-- statement:
--   The Trim Scales construction uses the replicated Half log rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L43-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L43-L62

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.TrimScales.replicatedHalf_log_rate_w3sum_ac885d1 {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun h : ℕ => Real.log (f h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => Real.log (replicatedHalf f n : ℝ) / Real.log n) atTop (𝓝 (a / 5)) := by sorry
