-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedParameters_native_log_atTop
-- name    : ThreeSum.WeightedGlobalSignedParameters.native_log_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:14:28.112308+00:00
-- url     : https://prove2.me/theorems/c6038eb8-243d-44e1-a27f-8bac29b3bef1
-- title:
--   Weighted Global Signed Parameters: native log at Top
-- statement:
--   The Weighted Global Signed Parameters construction uses the native log at Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedParameters.lean#L29-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedParameters.lean#L29-L42

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedParameters
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale WeightedGlobalOversizeOverhead
open WeightedGlobalOversizePrime WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology

theorem ThreeSum.WeightedGlobalSignedParameters.native_log_atTop {K : ℕ} (hK : 0<K) :
    Tendsto (fun m => Real.log (nativePrime K m : ℝ)) atTop atTop := by sorry
