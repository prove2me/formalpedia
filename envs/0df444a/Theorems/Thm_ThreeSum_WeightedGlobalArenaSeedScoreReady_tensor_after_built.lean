-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedScoreReady_tensor_after_built
-- name    : ThreeSum.WeightedGlobalArenaSeedScoreReady.tensor_after_built
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:16:40.994208+00:00
-- url     : https://prove2.me/theorems/de36ef27-6b18-4218-9dc6-be10f787d0a8
-- title:
--   Weighted Global Arena Seed Score Ready: tensor after built
-- statement:
--   The actual append/wanted outputs supply the host's source keys and
--   wanted records. The sole count-header write is proved from its literal store.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedScoreReady.lean#L70-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedScoreReady.lean#L70-L188

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSeedScoreReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaSeedScoreReady.tensor_after_built {lim : Limits} {depth K U seed : ℕ}
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
