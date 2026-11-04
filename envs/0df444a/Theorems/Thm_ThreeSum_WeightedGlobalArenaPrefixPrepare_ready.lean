-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPrepare_ready
-- name    : ThreeSum.WeightedGlobalArenaPrefixPrepare.ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:18:07.15926+00:00
-- url     : https://prove2.me/theorems/12bb56a3-3d37-49bd-beae-cd1634f24ab8
-- title:
--   Weighted Global Arena Prefix Prepare: ready
-- statement:
--   A single polynomial arena capacity bounds all actual header arithmetic;
--   free can be arbitrarily large subject only to the original memory limit.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean#L66-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepare.lean#L66-L194

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
import Theorems.Thm_ThreeSum_LightTernaryQueryPlan_ready
import Theorems.Thm_ThreeSum_LightWeightedQueryPlan_ready
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPrepare
open Light WeightedGlobalLocalParameters TernaryJointType WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaPrefixPrepare.ready {lim : Limits} {p m F j J n U0 a b scale depth : ℕ}
    (I : Input) (Q : WeightedGlobalGoodOutputCatalog.Output m) (μ : ℕ→ℤ)
    (hm : 0<m) (hw : (lim.space:ℤ)≤lim.word)
    (hcap : envelope (inputs p m F j J n U0 a b scale I Q)≤I.capacity)
    (hspace : finish I.free I.capacity≤lim.space)
    (hdepth : depth+LightWeightedGlobalPrefixSetup.N m (j+1)+5≤lim.depth)
    (hF : μ (addr I.free I.capacity 0+99)=(addr I.free I.capacity 50:ℤ))
    (hG : μ (addr I.free I.capacity 0+100)=(addr I.free I.capacity 51:ℤ))
    (hbudget : Seg μ (addr I.free I.capacity 3+41)
      (LightTernaryBudgetStep.oldValues (p^j) (p^j) (a^j) (9^j*(n*n)) (9^j*(n*n)) (U0*(b*scale)^j))) :
    PrepareReady (inputs p m F j J n U0 a b scale I Q) lim depth μ := by sorry
