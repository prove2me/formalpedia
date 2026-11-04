-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairCosts_next_le_encoderCount
-- name    : ThreeSum.SourceBandPairCosts.next_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:16:20.083846+00:00
-- url     : https://prove2.me/theorems/82f442c5-b34d-4b66-a79d-092bf995fa17
-- title:
--   Source Band Pair Costs: next le encoder Count
-- statement:
--   The Source Band Pair Costs construction uses the next le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairCosts.lean#L54-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairCosts.lean#L54-L66

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairCosts
open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData

theorem ThreeSum.SourceBandPairCosts.next_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    next base NL NR (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) ≤
      base+29*encoderCount n+9 := by sorry
