-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_repeated_native_family_factor_bound
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.repeated_native_family_factor_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:03:05.411447+00:00
-- url     : https://prove2.me/theorems/08f1db56-2400-4438-ac99-93d65b073408
-- title:
--   Weighted Global Oversize Overhead: repeated native family factor bound
-- statement:
--   The Weighted Global Oversize Overhead construction uses the repeated native family factor bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L290-L296
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L290-L296

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.repeated_native_family_factor_bound (K k c d m b r : ℕ)
    (hb : b ≤ c*(fixedLength m+1)^d) :
    (b*(nativeFamily K m k).length*
      rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)^r ≤
        (inflation K m)^(4*r)*(baseFactor K k c d m)^r := by sorry
