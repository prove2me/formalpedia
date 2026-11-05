-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceCountSeed.seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T14:17:37.902971+00:00
-- url     : https://prove2.me/theorems/5a967335-a1f5-4569-96a1-e7d3e5606a60
-- title:
--   seed
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceCountSeed.lean#L29-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceCountSeed.lean#L29-L120

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceSeed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCountSeed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceCountSeed
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceCountSeed.seed {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ)
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
