-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflation_lower
-- name    : ThreeSum.WeightedGlobalOversizePrime.inflation_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:29.288977+00:00
-- url     : https://prove2.me/theorems/5a0d3cd1-6bcb-44ef-acd6-6241a5cbf09e
-- title:
--   Weighted Global Oversize Prime: inflation lower
-- statement:
--   The Weighted Global Oversize Prime construction uses the inflation lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L102-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizePrime.lean#L102-L103

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

theorem ThreeSum.WeightedGlobalOversizePrime.inflation_lower {K : ℕ} (hK : 0 < K) (m : ℕ) : outputSize m ≤ inflation K m^K := by sorry
