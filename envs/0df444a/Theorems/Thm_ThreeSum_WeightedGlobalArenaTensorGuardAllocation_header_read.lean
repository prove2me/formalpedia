-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorGuardAllocation_header_read
-- name    : ThreeSum.WeightedGlobalArenaTensorGuardAllocation.header_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:15:56.867593+00:00
-- url     : https://prove2.me/theorems/235edabf-134e-4c27-a401-8d01524253e6
-- title:
--   Weighted Global Arena Tensor Guard Allocation: header read
-- statement:
--   The actual emitted header supplies every immutable host field. Its one
--   varying count cell is written later by the real SeedScore program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorGuardAllocation.lean#L37-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorGuardAllocation.lean#L37-L53

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceArithmetic
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixPreparedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorGuardAllocation
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTensorGuardAllocation
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaTensorGuardAllocation.header_read (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed : ℕ)
    (D : Data (config p r I A seed)) (μ : ℕ→ℤ) (ret : ℤ) (hr : 0<r)
    (hs : Seg μ (addr I.free I.capacity 1)
      (WeightedGlobalArenaHeaderAgreement.emittedHeader I p m F (r-1) Q ret)) :
    ∀i<106,i≠104→ μ (addr I.free I.capacity 1+i)=
      (setup (r := r) maps τ cap Q (sourceInput I A seed D)).argv.getD i 0 := by sorry
