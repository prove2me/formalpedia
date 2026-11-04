-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_native_source_cap_upper
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.native_source_cap_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:04:18.089982+00:00
-- url     : https://prove2.me/theorems/f184b2b9-47e0-4b3c-ac15-f8c187cffdd8
-- title:
--   Weighted Global Oversize Overhead: native source cap upper
-- statement:
--   The Weighted Global Oversize Overhead construction uses the native source cap upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L40-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L40-L54

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.native_source_cap_upper (K m : ℕ) :
    sourceCap m (nativePrime K m) ≤ 2^(2*fixedLength m+4) := by sorry
