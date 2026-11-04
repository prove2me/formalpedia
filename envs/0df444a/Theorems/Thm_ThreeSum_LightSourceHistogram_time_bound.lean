-- Prove2me | Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
-- name    : ThreeSum.LightSourceHistogram.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:33:33.671623+00:00
-- url     : https://prove2.me/theorems/621f60d9-666d-4e9b-b1c9-ba73c7f37e1d
-- title:
--   Light Source Histogram: time bound
-- statement:
--   The Light Source Histogram construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceHistogram.lean#L107-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceHistogram.lean#L107-L112

import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceHistogram
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceHistogram.time_bound (n p m U D : ℕ) :
    time n p m U D ≤
      278*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+13*m+63 := by sorry
