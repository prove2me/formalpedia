-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_native_cap_exponent_bound
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.native_cap_exponent_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:04:19.184708+00:00
-- url     : https://prove2.me/theorems/cc362770-0aa8-494d-a238-c9030de2407e
-- title:
--   Weighted Global Oversize Overhead: native cap exponent bound
-- statement:
--   The Weighted Global Oversize Overhead construction uses the native cap exponent bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L56-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L56-L67

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.native_cap_exponent_bound {K : ℕ} (hK : 0 < K) (m k : ℕ) :
    k*capExponent (nativePrime K m) (sourceCap m (nativePrime K m)) k ≤
      20*fixedLength m+8*k^2+26+k := by sorry
