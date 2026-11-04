-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalExecutableParameters_source_nonempty
-- name    : ThreeSum.WeightedGlobalExecutableParameters.source_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:02:26.892206+00:00
-- url     : https://prove2.me/theorems/dd1aefe7-1b03-4af4-8cbd-48baec25c537
-- title:
--   Weighted Global Executable Parameters: source nonempty
-- statement:
--   The Weighted Global Executable Parameters construction uses the source nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExecutableParameters.lean#L38-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExecutableParameters.lean#L38-L43

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryExecutable
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalExecutableParameters
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverGoodMaps
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters WeightedGlobalNativeCoverWitness WeightedGlobalCoverScale
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalExecutableParameters.source_nonempty {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k) (right : Bool) :
    0<(WeightedGlobalNativeCompleteFrontend.localRecords (maps K m k) (cap K m) right).length := by sorry
