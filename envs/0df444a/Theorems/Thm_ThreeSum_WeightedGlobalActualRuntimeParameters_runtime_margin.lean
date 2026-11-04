-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualRuntimeParameters_runtime_margin
-- name    : ThreeSum.WeightedGlobalActualRuntimeParameters.runtime_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:25:58.91452+00:00
-- url     : https://prove2.me/theorems/81064d09-e770-471c-a541-a268ce713d7c
-- title:
--   Weighted Global Actual Runtime Parameters: runtime margin
-- statement:
--   The Weighted Global Actual Runtime Parameters construction uses the runtime margin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualRuntimeParameters.lean#L19-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualRuntimeParameters.lean#L19-L32

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualRuntimeParameters
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalOversizePrime
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeRates WeightedGlobalSignedPadding
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalActualRuntimeParameters.runtime_margin {K m : ℕ} (hK : 100000000000000000000≤K) (c d : ℕ)
    (hgood : GoodBlock K m)
    (hover : overheadCharge (selectedMoment K) c d m<microAllowance K) :
    fullExponent K (selectedMoment K) c d m+microAllowance K+(1/1250000000:ℝ)<
      WeightedGlobalParameters.targetExponent:= by sorry
