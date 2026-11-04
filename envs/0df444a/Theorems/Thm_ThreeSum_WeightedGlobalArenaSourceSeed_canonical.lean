-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_canonical
-- name    : ThreeSum.WeightedGlobalArenaSourceSeed.canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:22:50.197247+00:00
-- url     : https://prove2.me/theorems/eb874dd6-9ec8-41a4-bb8e-ba42f357b910
-- title:
--   Weighted Global Arena Source Seed: canonical
-- statement:
--   Both source colors use the same literal bank addresses and occurrence
--   identifiers as the canonical tuple dictionaries.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceSeed.lean#L44-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceSeed.lean#L44-L108

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControls
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSeed
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceSeed
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries LightTernarySourceHost
open WeightedGlobalNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalArenaSourceSeed.canonical (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) (hF : 1<F) :
    Canonical (source (r := r) maps cap I right)
      (WeightedBankCanonical.enumeration (N m r) (cut m r)).word := by sorry
