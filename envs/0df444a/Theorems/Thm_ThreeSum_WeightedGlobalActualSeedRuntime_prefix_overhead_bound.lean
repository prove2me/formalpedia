-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_prefix_overhead_bound
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.prefix_overhead_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:19:58.629202+00:00
-- url     : https://prove2.me/theorems/4decb0b8-936c-47ce-83c2-5b8e7b8a64b4
-- title:
--   Weighted Global Actual Seed Runtime: prefix overhead bound
-- statement:
--   The Weighted Global Actual Seed Runtime construction uses the prefix overhead bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L509-L558
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L509-L558

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualSeedRuntime
open Real Light Filter
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalEntropyRates WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualSeedRuntime.prefix_overhead_bound {m j J p n nB nC nO carries : ℕ} {V : ℝ}
    (hj : 1≤j) (hJ : j≤J) (hcarries : 1≤carries)
    (hnB : nB≤n) (hnC : nC≤n) (hnO : nO≤n*carries)
    (h1 : 1≤V) (hn : (n:ℝ)≤V) (hp : (p:ℝ)^j≤V)
    (hbank : (WeightedGlobalDimensionBounds.bankSize m j:ℝ)≤V) :
    (prefixOverhead m j J p nB nC nO:ℝ)≤(overheadCoefficient m:ℝ)*(J+1:ℕ)*(carries:ℝ)*V:= by sorry
