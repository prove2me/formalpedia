-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCountReady_ready
-- name    : ThreeSum.WeightedGlobalArenaCountReady.ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:40:37.699698+00:00
-- url     : https://prove2.me/theorems/1b8b88d3-85ee-46b6-92ef-57191d506b9a
-- title:
--   Weighted Global Arena Count Ready: ready
-- statement:
--   Builds every actual frontend guard, including its per-query near plan,
--   from the canonical source/wanted arrays and scalar arena capacities.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCountReady.lean#L73-L216
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCountReady.lean#L73-L216

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceValues
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Theorems.Thm_ThreeSum_LightTernaryQueryPlan_ready
import Theorems.Thm_ThreeSum_LightWeightedQueryPlan_ready

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCountReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalBank TernaryCodeSemantics LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaCountReady.ready {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ)
    (localQ : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) (hF : 1<F) (hN : 0<N m r)
    (hw : (lim.space : ℤ)≤lim.word)
    (C : Capacity (lim := lim) (d := d) (r := r) maps τ cap I)
    (hcodes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ))))
    (hrecords : Seg μ (addr I.free I.capacity 19) (TernaryWantedBatchIndex.cells (entries (r := r) maps τ I)))
    (hleft : ∀i<I.nB, |leftWeight i|≤(I.weightCap : ℤ))
    (hright : ∀i<I.nC, |rightWeight i|≤(I.weightCap : ℤ)) :
    WeightedCountExecutionFactory.Ready (front (r := r) maps τ cap localQ I) lim d μ
      ((source (r := r) maps cap I false).values (WeightedBankCanonical.enumeration (N m r) (cut m r)).word leftWeight)
      ((source (r := r) maps cap I true).values (WeightedBankCanonical.enumeration (N m r) (cut m r)).word rightWeight) := by sorry
