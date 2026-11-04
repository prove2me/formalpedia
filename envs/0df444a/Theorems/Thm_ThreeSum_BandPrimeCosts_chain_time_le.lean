-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeCosts_chain_time_le
-- name    : ThreeSum.BandPrimeCosts.chain_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:33.550782+00:00
-- url     : https://prove2.me/theorems/999a117a-db40-4ba1-b2c8-2285417c5934
-- title:
--   Band Prime Costs: chain time le
-- statement:
--   The Band Prime Costs construction uses the chain time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L63-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L63-L70

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.BandPrimeCosts.chain_time_le (p g R s U levels : ℕ) :
    LightBandPrimeChain.time p g R s U levels ≤ 4*(levels+1)*core p g R s U := by sorry
