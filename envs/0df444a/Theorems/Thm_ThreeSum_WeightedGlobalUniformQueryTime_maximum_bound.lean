-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalUniformQueryTime_maximum_bound
-- name    : ThreeSum.WeightedGlobalUniformQueryTime.maximum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:13:51.980024+00:00
-- url     : https://prove2.me/theorems/ede536df-980a-497f-8175-09d6f97659ba
-- title:
--   Weighted Global Uniform Query Time: maximum bound
-- statement:
--   Uniform repricing uses the final prefix's query envelope. Earlier stages
--   retain their actual record counts; no bound by their smaller query maximum
--   is asserted.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryUniformQueryTime.lean#L60-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryUniformQueryTime.lean#L60-L85

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalUniformQueryTime
open WeightedGlobalArenaSourceSetup WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalActualPrefixRuntime WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalUniformQueryTime.maximum_bound {n U κ D E : ℕ} (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (hm : 0<m) (hn : 1<n) (hU : U≤n^κ)
    (hword : ∀j≤WeightedGlobalCoverScale.radixLength m n,
      WeightedGlobalFrontendResources.eulerBound (N m j) (valueCap (r:=j) maps cap I)≤D*(n+U+1)^E) :
    (maximum maps cap I (WeightedGlobalCoverScale.radixLength m n):ℝ)≤
      (coefficient m D E κ:ℝ)*(WeightedGlobalCoverScale.radixLength m n+1:ℕ)^3*
        WeightedGlobalCountFrontendBudget.envelope m (WeightedGlobalCoverScale.radixLength m n) := by sorry
