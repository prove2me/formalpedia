-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairCosts_time_le_encoderCount
-- name    : ThreeSum.SourceBandPairCosts.time_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:41:06.455328+00:00
-- url     : https://prove2.me/theorems/5ed8cd54-fcf5-4681-9d48-e9ed7485c74e
-- title:
--   Source Band Pair Costs: time le encoder Count
-- statement:
--   The Source Band Pair Costs construction uses the time le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairCosts.lean#L44-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairCosts.lean#L44-L52

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_WeightedCache3SUM_Alias_8b3592271bea283a

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairCosts
open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData

theorem ThreeSum.SourceBandPairCosts.time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandPair.time NL NR (bandSize n) p
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) U D ≤
      (2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+3905)*encoderCount n+3139 := by sorry
