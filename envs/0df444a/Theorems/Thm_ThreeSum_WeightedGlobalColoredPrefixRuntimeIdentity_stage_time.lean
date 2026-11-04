-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPrefixRuntimeIdentity_stage_time
-- name    : ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity.stage_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:31:49.016199+00:00
-- url     : https://prove2.me/theorems/3c037242-cc45-410c-bca0-708acd0993db
-- title:
--   Weighted Global Colored Prefix Runtime Identity: stage time
-- statement:
--   The Weighted Global Colored Prefix Runtime Identity construction uses the stage time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPrefixRuntimeIdentity.lean#L66-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPrefixRuntimeIdentity.lean#L66-L75

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLoop
open LightWeightedGlobalSeedScoreFactory WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup
open WeightedGlobalActualSeedRuntime
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredPrefixRuntimeIdentity.stage_time (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))] (j : ℕ) :
    let S:=setup P n free menu c A B C μ
    prefixStageTime (k:=P.k) P.maps P.output S.input S.arrays (prefixData S (j+1))=S.timeAt j := by sorry
