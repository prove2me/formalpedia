-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalMomentSourceProgram_values_positions
-- name    : ThreeSum.LightWeightedGlobalMomentSourceProgram.values_positions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:49:56.917846+00:00
-- url     : https://prove2.me/theorems/4dc7619c-c2c7-4fdc-9aa1-feb1a80e0c7b
-- title:
--   Light Weighted Global Moment Source Program: values positions
-- statement:
--   Backend argument locations are ordinary local-variable reads, and give
--   exactly the source/count host's complete 106-argument runtime frame.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentSourceProgram.lean#L64-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentSourceProgram.lean#L64-L77

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentSourceProgram
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalMomentSourceProgram
open Light TernaryWeightChannels

theorem ThreeSum.LightWeightedGlobalMomentSourceProgram.values_positions (originalB nB originalC nC leftWeight rightWeight matrix count out : ℕ)
    (backend : List ℤ) (hlen : backend.length=106) :
    LightTernaryMomentChannelStep.values positions
      (LightTernaryMomentChannelStep.args originalB nB originalC nC
        leftWeight rightWeight matrix count out backend)=backend := by sorry
