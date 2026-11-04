-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeCosts_aggregate_time_le_w3sum_ac885d1
-- name    : ThreeSum.BandPrimeCosts.aggregate_time_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:52.873578+00:00
-- url     : https://prove2.me/theorems/a34b0e5d-c9e6-4c72-b930-d729b5818b40
-- title:
--   Band Prime Costs: aggregate time le
-- statement:
--   The Band Prime Costs construction uses the aggregate time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L30-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L30-L42

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.BandPrimeCosts.aggregate_time_le_w3sum_ac885d1 (p g R s U : ℕ) :
    LightBandWeightedScore.time p g R s U ≤ 2*(R+1)*(s+1)*unit p g U := by sorry
