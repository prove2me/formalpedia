-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedFamilyMargin_family_log_bound
-- name    : ThreeSum.WeightedGlobalPairedFamilyMargin.family_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:29:42.346924+00:00
-- url     : https://prove2.me/theorems/25efd614-c3a7-4223-9083-5f027ade1538
-- title:
--   Weighted Global Paired Family Margin: family log bound
-- statement:
--   The Weighted Global Paired Family Margin construction uses the family log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedFamilyMargin.lean#L37-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedFamilyMargin.lean#L37-L74

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedFamilyMargin
open Filter Real WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalParameters
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalPairedFamilyMargin.family_log_bound {K m : ℕ} (hK : 0<K) (hm : 0<m) (k : ℕ) :
    Real.log (9*(nativeFamily K m k).length : ℝ)/((fixedLength m : ℝ)*Real.log 2) ≤
      baseRate m+4*inflationRate K m := by sorry
