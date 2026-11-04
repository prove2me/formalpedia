-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalUniformQueryTime_allocated_word
-- name    : ThreeSum.WeightedGlobalUniformQueryTime.allocated_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:13:49.346425+00:00
-- url     : https://prove2.me/theorems/e7c1f517-93b8-4f25-af09-8a9b93e3badf
-- title:
--   Weighted Global Uniform Query Time: allocated word
-- statement:
--   The already allocated division words provide the uniform logarithmic
--   width bound, including arbitrary actual source values and multiplicities.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryUniformQueryTime.lean#L89-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryUniformQueryTime.lean#L89-L101

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

theorem ThreeSum.WeightedGlobalUniformQueryTime.allocated_word {τ cap M b K H drift scale n U r : ℕ}
    (maps : Fin F→Weight m p) (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (hr : r≤Nat.clog M (n^2)) (hB : I.nB≤n) (hC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U) :
    WeightedGlobalFrontendResources.eulerBound (N m r) (valueCap (r:=r) maps cap I)≤
      (256*(Alloc.D+1))*(n+U+1)^Alloc.E := by sorry
