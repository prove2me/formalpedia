-- Prove2me | Theorems.Thm_ThreeSum_LightSelectedPrime_time_bound_w3sum_ac885d1
-- name    : ThreeSum.LightSelectedPrime.time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:38.518746+00:00
-- url     : https://prove2.me/theorems/5edc6c98-2c79-4df9-bbaa-59a750eff259
-- title:
--   Light Selected Prime: time bound
-- statement:
--   The Light Selected Prime construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSelectedPrime.lean#L129-L143
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSelectedPrime.lean#L129-L143

import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSelectedPrime
open Light LocalCoverBounds LightResidues
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSelectedPrime.time_bound_w3sum_ac885d1 (N : ℕ) : time N ≤ 6000*(N+2)^3 := by sorry
