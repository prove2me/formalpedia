-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflated_frequency_scale
-- name    : ThreeSum.WeightedGlobalOversizePrime.inflated_frequency_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:01.383628+00:00
-- url     : https://prove2.me/theorems/edc96a77-e9c7-4843-8899-75047802e5be
-- title:
--   Weighted Global Oversize Prime: inflated frequency scale
-- statement:
--   The Weighted Global Oversize Prime construction uses the inflated frequency scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L138-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L138-L152

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

theorem ThreeSum.WeightedGlobalOversizePrime.inflated_frequency_scale {K : ℕ} (hK : 0 < K) (m : ℕ) :
    4*(nativePrime K m)^4*3^16 ≤ inflatedFrequency K m*Fintype.card (WeightedGlobalCoverGoodMaps.ActualEdge m)^2 := by sorry
