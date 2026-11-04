-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_time_le_budget
-- name    : ThreeSum.EncodedColorPrimeCosts.time_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:37:57.962663+00:00
-- url     : https://prove2.me/theorems/a9748395-f9b1-41d0-8ddb-a32c33de9c6d
-- title:
--   Encoded Color Prime Costs: time le budget
-- statement:
--   The Encoded Color Prime Costs construction uses the time le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeCosts.lean#L53-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeCosts.lean#L53-L58

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_time_le_budget

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds

theorem ThreeSum.EncodedColorPrimeCosts.time_le_budget {nA nB nC n : ℕ} (k : ℕ) (hn : 0 < n)
    (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    LightEncodedColorPrime.time (maxMod n) nA nB nC (bandSize n) (radix n) (primeWindow n) (n^k) ≤
      BandPrimeCosts.timeBudget k n+1160 := by sorry
