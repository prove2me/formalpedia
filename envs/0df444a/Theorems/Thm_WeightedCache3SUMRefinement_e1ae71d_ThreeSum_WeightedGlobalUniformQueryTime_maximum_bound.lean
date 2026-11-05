-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalUniformQueryTime_maximum_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime.maximum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T14:34:02.698214+00:00
-- url     : https://prove2.me/theorems/de1513f1-86a8-492c-8059-416cda1456b6
-- title:
--   maximum_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryUniformQueryTime.lean#L60-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryUniformQueryTime.lean#L60-L85

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime
open WeightedGlobalArenaSourceSetup WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalActualPrefixRuntime WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalUniformQueryTime.maximum_bound {n U κ D E : ℕ} (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (hm : 0<m) (hn : 1<n) (hU : U≤n^κ)
    (hword : ∀j≤WeightedGlobalCoverScale.radixLength m n,
      WeightedGlobalFrontendResources.eulerBound (N m j) (valueCap (r:=j) maps cap I)≤D*(n+U+1)^E) :
    (maximum maps cap I (WeightedGlobalCoverScale.radixLength m n):ℝ)≤
      (coefficient m D E κ:ℝ)*(WeightedGlobalCoverScale.radixLength m n+1:ℕ)^3*
        WeightedGlobalCountFrontendBudget.envelope m (WeightedGlobalCoverScale.radixLength m n) := by sorry
