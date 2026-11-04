-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeCosts_setup_time_le_budget_w3sum_ac885d1
-- name    : ThreeSum.BandPrimeCosts.setup_time_le_budget_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:36.938196+00:00
-- url     : https://prove2.me/theorems/61eedca4-e2f0-4f1c-9209-e2f4f17bb2cc
-- title:
--   Band Prime Costs: setup time le budget
-- statement:
--   The Band Prime Costs construction uses the setup time le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L115-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeCosts.lean#L115-L129

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem ThreeSum.BandPrimeCosts.setup_time_le_budget_w3sum_ac885d1 {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*bandCount n^2) :
    LightBandPrimeSetup.time (maxMod n) (bandSize n) R (radix n) (primeWindow n) (n^k) ≤
      timeBudget k n := by sorry
