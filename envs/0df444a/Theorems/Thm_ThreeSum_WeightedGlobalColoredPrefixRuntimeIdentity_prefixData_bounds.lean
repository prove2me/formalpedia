-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPrefixRuntimeIdentity_prefixData_bounds
-- name    : ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity.prefixData_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:15:22.620471+00:00
-- url     : https://prove2.me/theorems/9e0efd6e-2743-4fb1-98d0-425f01d49b6c
-- title:
--   Weighted Global Colored Prefix Runtime Identity: prefix Data bounds
-- statement:
--   The Weighted Global Colored Prefix Runtime Identity construction uses the prefix Data bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPrefixRuntimeIdentity.lean#L42-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPrefixRuntimeIdentity.lean#L42-L48

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLoop
open LightWeightedGlobalSeedScoreFactory WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup
open WeightedGlobalActualSeedRuntime
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity.prefixData_bounds {p m F K N : ℕ} [Fact p.Prime]
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    (S : Setup p m F K N E) (j seed : ℕ) :
    (prefixData S j seed).bB=S.featureBound ∧
    (prefixData S j seed).bC=S.featureBound ∧
    (prefixData S j seed).bO=S.featureBound := by sorry
