-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeCosts_setup_time_le
-- name    : ThreeSum.BandPrimeCosts.setup_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:13.295857+00:00
-- url     : https://prove2.me/theorems/021fac72-24de-4798-9792-7e517058c521
-- title:
--   Band Prime Costs: setup time le
-- statement:
--   The Band Prime Costs construction uses the setup time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L72-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L72-L84

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.BandPrimeCosts.setup_time_le (p g R M y U : ℕ) :
    LightBandPrimeSetup.time p g R M y U ≤ LightPrimePool.time y+
      5*(LightBandPrimeDepth.depth M y+1)*(R+1)*(LightPrimePool.size y+1)^2*unit p g U := by sorry
