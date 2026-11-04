-- Prove2me | Theorems.Thm_ThreeSum_TrimScales_fullOutputs_eventually_le
-- name    : ThreeSum.TrimScales.fullOutputs_eventually_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:11.898807+00:00
-- url     : https://prove2.me/theorems/2be610d4-cf9f-47ce-91d1-baa0c97ebac3
-- title:
--   Trim Scales: full Outputs eventually le
-- statement:
--   The Trim Scales construction uses the full Outputs eventually le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L281-L283
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L281-L283

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.TrimScales.fullOutputs_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (fullOutputs n : ℝ) ≤ (n : ℝ) ^ (2 * Parameters.E / 5 + d) := by sorry
