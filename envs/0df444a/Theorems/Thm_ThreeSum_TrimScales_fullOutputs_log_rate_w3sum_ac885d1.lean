-- Prove2me | Theorems.Thm_ThreeSum_TrimScales_fullOutputs_log_rate_w3sum_ac885d1
-- name    : ThreeSum.TrimScales.fullOutputs_log_rate_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:31.766872+00:00
-- url     : https://prove2.me/theorems/af3045b9-d3d4-4390-b469-ca626a2de2d7
-- title:
--   Trim Scales: full Outputs log rate
-- statement:
--   The Trim Scales construction uses the full Outputs log rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L266-L279
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L266-L279

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.TrimScales.fullOutputs_log_rate_w3sum_ac885d1 :
    Tendsto (fun n : ℕ => Real.log (fullOutputs n : ℝ) / Real.log n) atTop
      (𝓝 (2 * Parameters.E / 5)) := by sorry
