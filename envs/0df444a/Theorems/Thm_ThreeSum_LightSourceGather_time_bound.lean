-- Prove2me | Theorems.Thm_ThreeSum_LightSourceGather_time_bound
-- name    : ThreeSum.LightSourceGather.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:41.939198+00:00
-- url     : https://prove2.me/theorems/dae856df-58eb-43a1-aaa5-e32bb77eff92
-- title:
--   Light Source Gather: time bound
-- statement:
--   The Light Source Gather construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceGather.lean#L156-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceGather.lean#L156-L158

import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceGather
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceGather.time_bound (n U : ℕ) : time n U ≤ 157*n*(Nat.log 2 (U+1)+1)+6 := by sorry
