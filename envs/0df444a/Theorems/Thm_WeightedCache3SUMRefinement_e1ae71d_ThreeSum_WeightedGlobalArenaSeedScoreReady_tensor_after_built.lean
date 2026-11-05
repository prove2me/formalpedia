-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSeedScoreReady_tensor_after_built
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSeedScoreReady.tensor_after_built
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:43:06.024945+00:00
-- url     : https://prove2.me/theorems/2c89ddae-a7ac-46b1-878d-32fe8db65f0c
-- title:
--   tensor_after_built
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSeedScoreReady.lean#L70-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSeedScoreReady.lean#L70-L188

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaTensorReady
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSeedScoreReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSeedScoreReady.tensor_after_built {lim : Limits} {depth K U seed : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ ν : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (P : AppendGuard (config p r I A seed) D lim depth μ)
    (G : TensorGuard (lim := lim) (depth := depth) (K := K) (U := U) maps τ cap Q I A D μ L R)
    (H : Built (config p r I A seed) D (4^fixedLength m) F
      (WeightedGlobalGoodOutputCatalog.raws maps τ) (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
      (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) μ ν) :
    LightWeightedGlobalTensorFactory.Ready (setup (r := r) maps τ cap Q (sourceInput I A seed D))
      lim (depth+1) K A.J (addr I.free I.capacity 1) A.leftTagged A.rightTagged
      (addr I.free I.capacity 23) (addr I.free I.capacity 24) (addr I.free I.capacity 25)
      (addr I.free I.capacity 26) (addr I.free I.capacity 27)
      (Function.update ν (addr I.free I.capacity 1+104)
        (D.H (4^fixedLength m) F (WeightedGlobalGoodOutputCatalog.raws maps τ)
          (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) : ℤ))
      L R U (WeightedGlobalNativeMomentBounds.scoreBound (setup (r := r) maps τ cap Q (sourceInput I A seed D))) := by sorry
