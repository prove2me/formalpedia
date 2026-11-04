-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeCosts_unit_le_budget
-- name    : ThreeSum.BandPrimeCosts.unit_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:21.286475+00:00
-- url     : https://prove2.me/theorems/1f954b90-4ccd-444f-a92c-e5263fabfab1
-- title:
--   Band Prime Costs: unit le budget
-- statement:
--   The Band Prime Costs construction uses the unit le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L99-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L99-L109

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.BandPrimeCosts.unit_le_budget {n : ℕ} (k : ℕ) (hn : 0 < n) :
    unit (maxMod n) (bandSize n) (n^k) ≤ 3*perTripleBudget k n := by sorry
