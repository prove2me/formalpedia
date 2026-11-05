-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run_full
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalControllerFactory.Candidate.run_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T14:26:12.321106+00:00
-- url     : https://prove2.me/theorems/2e593db2-e0ac-4a81-848f-c3d4a7364331
-- title:
--   run_full
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryControllerFull.lean#L30-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryControllerFull.lean#L30-L83

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFull
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFull
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run_full

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalControllerFactory
open Light LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalControllerFactory.Candidate.run_full {C : Config} [Fact C.p.Prime] {D : Candidate C} {lim : Limits}
    {depth K R S : ℕ} {raws : List ℤ} {words maps : List ℕ} {μ : ℕ→ℤ}
    (G : D.FullGuard lim depth K R S raws words maps μ) :
    Meets lim (LightWeightedGlobalSeedScore.program C.p R S K raws words maps
      D.host.left.xs D.host.left.ys D.host.left.zs D.host.right.xs D.host.right.ys D.host.right.zs)
      176 depth C.argv μ (D.runtime K R S raws words maps)
      (fun r ν=>r=D.data.flag ∧ D.FullDone K R S raws words maps μ ν) := by sorry
