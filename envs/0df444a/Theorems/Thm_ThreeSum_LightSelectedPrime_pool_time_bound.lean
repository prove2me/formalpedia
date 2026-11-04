-- Prove2me | Theorems.Thm_ThreeSum_LightSelectedPrime_pool_time_bound
-- name    : ThreeSum.LightSelectedPrime.pool_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:39.524197+00:00
-- url     : https://prove2.me/theorems/af02fd22-35fb-492a-8da2-146bd45c6d3c
-- title:
--   Light Selected Prime: pool time bound
-- statement:
--   The Light Selected Prime construction uses the pool time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSelectedPrime.lean#L113-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSelectedPrime.lean#L113-L127

import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
set_option autoImplicit false
open ThreeSum ThreeSum.LightSelectedPrime
open Light LocalCoverBounds LightResidues
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSelectedPrime.pool_time_bound (y : ℕ) : LightPrimePool.time y ≤ 5000*(y+1)^3 := by sorry
