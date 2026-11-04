-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run_full
-- name    : ThreeSum.LightWeightedGlobalControllerFactory.Candidate.run_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:20:22.992253+00:00
-- url     : https://prove2.me/theorems/f54286f5-d06b-426a-8dd8-1b1b5a081b59
-- title:
--   Candidate: run full
-- statement:
--   Strong candidate execution retains every actual next-prefix key and
--   literal wanted record, including the real dynamic header count.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryControllerFull.lean#L30-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryControllerFull.lean#L30-L83

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFull
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFactory
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run_full

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalControllerFactory
open Light LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalControllerFactory.Candidate.run_full {C : Config} [Fact C.p.Prime] {D : Candidate C} {lim : Limits}
    {depth K R S : ℕ} {raws : List ℤ} {words maps : List ℕ} {μ : ℕ→ℤ}
    (G : D.FullGuard lim depth K R S raws words maps μ) :
    Meets lim (LightWeightedGlobalSeedScore.program C.p R S K raws words maps
      D.host.left.xs D.host.left.ys D.host.left.zs D.host.right.xs D.host.right.ys D.host.right.zs)
      176 depth C.argv μ (D.runtime K R S raws words maps)
      (fun r ν=>r=D.data.flag ∧ D.FullDone K R S raws words maps μ ν) := by sorry
