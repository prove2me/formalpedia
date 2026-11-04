-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_small_overhead_eventually
-- name    : ThreeSum.WeightedGlobalOversizeOverhead.small_overhead_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:01:54.494196+00:00
-- url     : https://prove2.me/theorems/610902ef-db55-491a-898c-4473b61becdc
-- title:
--   Weighted Global Oversize Overhead: small overhead eventually
-- statement:
--   The Weighted Global Oversize Overhead construction uses the small overhead eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L202-L205
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeOverhead.lean#L202-L205

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

theorem ThreeSum.WeightedGlobalOversizeOverhead.small_overhead_eventually {K : ℕ} (hK : 0 < K) (c d : ℕ) :
    ∀ᶠ m : ℕ in atTop, overheadCharge (selectedMoment K) c d m < microAllowance K := by sorry
