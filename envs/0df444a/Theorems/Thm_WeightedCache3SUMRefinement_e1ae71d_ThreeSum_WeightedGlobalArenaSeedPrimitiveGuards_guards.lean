-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSeedPrimitiveGuards_guards
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSeedPrimitiveGuards.guards
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:53:20.739877+00:00
-- url     : https://prove2.me/theorems/0a2dd31f-7ee6-45be-9a34-8a18b0f53675
-- title:
--   guards
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSeedPrimitiveGuards.lean#L63-L205
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSeedPrimitiveGuards.lean#L63-L205

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSeedPrimitiveGuards
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 8000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSeedPrimitiveGuards.guards {lim : Limits} {depth seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (A : Inputs)
    (D : Data (config p r I A seed)) (μ : ℕ→ℤ)
    (M : Reads I A seed D μ positionCap) (hw : (lim.space : ℤ)≤lim.word)
    (hend : finish I.free I.capacity≤lim.space)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity) (hnO : I.requesterCount≤I.capacity)
    (hJ : A.J+2≤I.capacity) (hspan : A.J*p^(r-1)≤I.capacity)
    (hhist : p^(r-1)*p≤I.capacity)
    (hwanted : 3*I.requesterCount*(F*WeightedGlobalGoodOutputCatalog.cap m p τ)^r≤I.capacity)
    (hdiv : Nat.log 2 (2*rawCap m p r+1)+2≤I.capacity)
    (hword : (word maps τ I A seed positionCap D : ℤ)≤lim.word)
    (hd : depth+r+6<lim.depth) (hF : 1<F) (hτ : 0<τ)
    (hraw : 1≤(WeightedGlobalGoodOutputCatalog.raws maps τ).length) :
    AppendGuard (config p r I A seed) D lim depth μ ∧
    SpanGuard (config p r I A seed) D lim μ ∧
    WantedGuard (config p r I A seed) D lim depth (4^fixedLength m) F
      (F*WeightedGlobalGoodOutputCatalog.cap m p τ) (rawCap m p r)
      (WeightedGlobalGoodOutputCatalog.raws maps τ) (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
      (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) μ ∧
    CollisionGuard (config p r I A seed) D lim (4^fixedLength m) F
      (WeightedGlobalGoodOutputCatalog.raws maps τ) (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
      (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) := by sorry
