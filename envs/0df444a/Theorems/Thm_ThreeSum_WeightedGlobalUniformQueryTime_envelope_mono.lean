-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalUniformQueryTime_envelope_mono
-- name    : ThreeSum.WeightedGlobalUniformQueryTime.envelope_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:22:32.454362+00:00
-- url     : https://prove2.me/theorems/45f36d23-7b48-44ba-85b0-5499971626a2
-- title:
--   Weighted Global Uniform Query Time: envelope mono
-- statement:
--   The Weighted Global Uniform Query Time construction uses the envelope mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryUniformQueryTime.lean#L33-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryUniformQueryTime.lean#L33-L44

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

theorem ThreeSum.WeightedGlobalUniformQueryTime.envelope_mono {j R : ℕ} (hj : j≤R) :
    WeightedGlobalCountFrontendBudget.envelope m j≤WeightedGlobalCountFrontendBudget.envelope m R := by sorry
