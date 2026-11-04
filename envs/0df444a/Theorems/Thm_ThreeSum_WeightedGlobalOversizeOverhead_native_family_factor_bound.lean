-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_native_family_factor_bound
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.native_family_factor_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:03:48.977131+00:00
-- url     : https://prove2.me/theorems/ad876fb2-9b4a-4148-8b30-8691411b1479
-- title:
--   Weighted Global Oversize Overhead: native family factor bound
-- statement:
--   The exact full native-family length splits into the separately priced
--   S^4 part and the base factor that includes tau and every carry choice.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L276-L288
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L276-L288

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalOversizeOverhead.native_family_factor_bound (K k c d m b : ℕ)
    (hb : b ≤ c*(fixedLength m+1)^d) :
    b*(nativeFamily K m k).length*
      rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k ≤
        (inflation K m)^4*baseFactor K k c d m := by sorry
