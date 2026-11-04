-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed
-- name    : ThreeSum.WeightedGlobalArenaSourceSeed.seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:17:35.679768+00:00
-- url     : https://prove2.me/theorems/f14a6383-e5f1-4b7c-9c8c-77c3b9a057a3
-- title:
--   Weighted Global Arena Source Seed: seed
-- statement:
--   The literal canonical source has all its pure preconditions. No source
--   execution receipt or mathematical source-value oracle is an input.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceSeed.lean#L133-L198
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceSeed.lean#L133-L198

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

theorem ThreeSum.WeightedGlobalArenaSourceSeed.seed {lim : Limits} {d : ℕ} {μ : ℕ→ℤ} {weight : ℕ→ℤ}
    (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) (hF : 1<F)
    (hw : (lim.space : ℤ)≤lim.word)
    (G : WeightedGlobalArenaSourceLayout.Geometry (source (r := r) maps cap I right) lim.space)
    (W : WeightedGlobalArenaSourceControls.Controls (r := r) maps cap I right lim d)
    (M : Memory (r := r) maps cap I right lim μ weight) :
    TernarySourceExecutionFactory.Seed (source (r := r) maps cap I right) lim d μ weight
      (WeightedBankCanonical.enumeration (N m r) (cut m r)).word := by sorry
