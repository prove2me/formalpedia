-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_seed_polynomial_bound
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.seed_polynomial_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:19:40.433675+00:00
-- url     : https://prove2.me/theorems/50eb80aa-b46f-4ec0-a79c-3133cc5af49d
-- title:
--   Weighted Global Actual Seed Runtime: seed polynomial bound
-- statement:
--   The Weighted Global Actual Seed Runtime construction uses the seed polynomial bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L280-L283
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L280-L283

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

theorem ThreeSum.WeightedGlobalActualSeedRuntime.seed_polynomial_bound (K p B J j : ℕ) (hj : j≤J) :
    seedCoefficient K J p B (p*(p+1)^j) j≤seedPolynomialC K p B*(J+1)^seedPolynomialD K p B:= by sorry
