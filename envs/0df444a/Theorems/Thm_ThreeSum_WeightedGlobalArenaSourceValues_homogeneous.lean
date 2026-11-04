-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceValues_homogeneous
-- name    : ThreeSum.WeightedGlobalArenaSourceValues.homogeneous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:22:23.974008+00:00
-- url     : https://prove2.me/theorems/80cd22bb-82fb-4b97-a901-cbd9edafb68b
-- title:
--   Weighted Global Arena Source Values: homogeneous
-- statement:
--   The Weighted Global Arena Source Values construction uses the homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceValues.lean#L19-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceValues.lean#L19-L35

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceValues
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceValues
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend LightTernarySourceHost
open scoped BigOperators
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalArenaSourceValues.homogeneous (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (weight : ℕ→ℤ) (g : ℕ) :
    ∀ W, (source (r := r) maps cap I right).values
      (WeightedBankCanonical.enumeration (N m r) (cut m r)).word weight g W≠0 →
      WeightedGlobalBank.rank W=r*alphaRank m := by sorry
