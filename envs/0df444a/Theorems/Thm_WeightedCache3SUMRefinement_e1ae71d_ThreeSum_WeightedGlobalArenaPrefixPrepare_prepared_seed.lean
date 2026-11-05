-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixPrepare_prepared_seed
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixPrepare.prepared_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:47.772651+00:00
-- url     : https://prove2.me/theorems/06df5259-a777-4122-a446-4f2f8ffa63b7
-- title:
--   prepared_seed
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean#L206-L222
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean#L206-L222

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPrepare
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixPrepare
open Light WeightedGlobalLocalParameters TernaryJointType WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixPrepare.prepared_seed {p m F j n U0 a b scale seedCount newSpan : ℕ} (I : Input)
    (A : WeightedGlobalArenaSeedCandidate.Inputs) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    {μ ν : ℕ→ℤ}
    (H : Prepared (inputs p m F j A.J n U0 a b scale I Q) μ ν)
    (hcap : 106≤I.capacity)
    (hseed : Seg μ (addr I.free I.capacity 3)
      (LightWeightedGlobalPrefixFinish.header (WeightedGlobalArenaSeedCandidate.config p j I A 0)
        seedCount (p^j) (p^j) (a^j) (9^j*n^2) (9^j*n^2) (U0*(b*scale)^j) newSpan)) :
    Seg ν (addr I.free I.capacity 3)
      (LightWeightedGlobalPrefixFinish.header (WeightedGlobalArenaSeedCandidate.config p (j+1) I A 0)
        seedCount (p^(j+1)) (p^(j+1)) (a^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
        (U0*(b*scale)^(j+1)) newSpan) := by sorry
