-- Prove2me | Theorems.Thm_ThreeSum_LightGlobalSizes_time_bound
-- name    : ThreeSum.LightGlobalSizes.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:34.253823+00:00
-- url     : https://prove2.me/theorems/c17fade7-099a-4348-8929-53bb13c08c08
-- title:
--   Light Global Sizes: time bound
-- statement:
--   The Light Global Sizes construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean#L166-L173
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean#L166-L173

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_BandScales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalSizes
set_option maxHeartbeats 1000000
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightGlobalSizes.time_bound (C J mu : ℕ) :
    time C J mu ≤ 1000*(J+mu+root C J+divisor mu+1) := by sorry
