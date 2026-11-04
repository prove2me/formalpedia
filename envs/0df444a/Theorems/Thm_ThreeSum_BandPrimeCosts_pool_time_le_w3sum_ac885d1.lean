-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeCosts_pool_time_le_w3sum_ac885d1
-- name    : ThreeSum.BandPrimeCosts.pool_time_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:22.514936+00:00
-- url     : https://prove2.me/theorems/69d37232-ba38-4a0a-a11c-435d6640b6a5
-- title:
--   Band Prime Costs: pool time le
-- statement:
--   The Band Prime Costs construction uses the pool time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L86-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L86-L97

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.BandPrimeCosts.pool_time_le_w3sum_ac885d1 (y : ℕ) : LightPrimePool.time y ≤ 100000*(y+1)^3 := by sorry
