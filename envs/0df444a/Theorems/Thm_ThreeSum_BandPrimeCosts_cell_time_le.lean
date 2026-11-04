-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeCosts_cell_time_le
-- name    : ThreeSum.BandPrimeCosts.cell_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:01.554892+00:00
-- url     : https://prove2.me/theorems/74971663-799d-4272-ab6a-f22bbf3e4a07
-- title:
--   Band Prime Costs: cell time le
-- statement:
--   The Band Prime Costs construction uses the cell time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L24-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L24-L28

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.BandPrimeCosts.cell_time_le (p g s U : ℕ) :
    LightBandWeightedScoreCell.time p g s U ≤ (s+1)*unit p g U := by sorry
