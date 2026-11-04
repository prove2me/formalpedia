-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPrepare_prepared_seed
-- name    : ThreeSum.WeightedGlobalArenaPrefixPrepare.prepared_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:18:34.830184+00:00
-- url     : https://prove2.me/theorems/96677241-d2fc-4d98-9929-55c7c38cc7ba
-- title:
--   Weighted Global Arena Prefix Prepare: prepared seed
-- statement:
--   The actual ten preparation writes give the exact positive-prefix seed
--   header, including the incremented budget denominators and thresholds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean#L206-L222
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean#L206-L222

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPrepare
open Light WeightedGlobalLocalParameters TernaryJointType WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaPrefixPrepare.prepared_seed {p m F j n U0 a b scale seedCount newSpan : ℕ} (I : Input)
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
