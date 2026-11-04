-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceHashes_time_bound
-- name    : ThreeSum.LightBlockSourceHashes.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:40.622587+00:00
-- url     : https://prove2.me/theorems/338a5baa-c547-4c62-8185-0ff510463979
-- title:
--   Light Block Source Hashes: time bound
-- statement:
--   The Light Block Source Hashes construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceHashes.lean#L196-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceHashes.lean#L196-L201

import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceHashes
open Light BlockCoefficientRows
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBlockSourceHashes.time_bound (J L n : ℕ) :
    time J L n ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+200 := by sorry
