-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
-- name    : ThreeSum.WeightedGlobalArenaSourceCountSeed.seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:45:30.902818+00:00
-- url     : https://prove2.me/theorems/66350a6d-27d5-44d4-8d4f-d624f1e2aa8c
-- title:
--   Weighted Global Arena Source Count Seed: seed
-- statement:
--   The Weighted Global Arena Source Count Seed construction uses the seed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceCountSeed.lean#L29-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceCountSeed.lean#L29-L120

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSeed
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceCountSeed
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaSourceCountSeed.seed {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ)
    (localQ : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) (hF : 1<F) (hN : 0<N m r)
    (hw : (lim.space : ℤ)≤lim.word)
    (C : WeightedGlobalArenaCountReady.Capacity (lim := lim) (d := d+1) (r := r) maps τ cap I)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity)
    (hprefix : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 28)
    (hlocal : ∀right, 0<(localRecords maps cap right).length)
    (G : ∀right, WeightedGlobalArenaSourceLayout.Geometry (source (r := r) maps cap I right) lim.space)
    (W : ∀right, WeightedGlobalArenaSourceControls.Controls (r := r) maps cap I right lim (d+1))
    (M : Reads (r := r) maps τ I μ)
    (hleft : ∀i<I.nB, |leftWeight i|≤(I.weightCap : ℤ))
    (hright : ∀i<I.nC, |rightWeight i|≤(I.weightCap : ℤ)) :
    WeightedSourceCountExecutionFactory.Seed (setup (r := r) maps τ cap localQ I) lim d
      (addr I.free I.capacity 28) μ leftWeight rightWeight := by sorry
