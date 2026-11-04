-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGlobalPreludeTime_uniform_eventually
-- name    : ThreeSum.WeightedGlobalGlobalPreludeTime.uniform_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:36:05.435009+00:00
-- url     : https://prove2.me/theorems/3c8b1f22-228a-4140-8b48-70d8c5f08d9e
-- title:
--   Weighted Global Global Prelude Time: uniform eventually
-- statement:
--   All actual global-prelude overhead is subpolynomial for the selected
--   fixed local alphabet, uniformly over arbitrary caller free addresses.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeTime.lean#L70-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalPreludeTime.lean#L70-L82

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalPreludeResources
import Definitions.Def_Submission_Weighted_Global_LightExtensionBackendSetupBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsTime
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalPreludeTime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalGlobalPreludeTime
open Light LightWeightedGlobalGlobalPrelude LightExtensionBackendLayout
open Filter WeightedGlobalCoverScale
set_option maxHeartbeats 4000000

theorem ThreeSum.WeightedGlobalGlobalPreludeTime.uniform_eventually {m b p K κ : ℕ} [Fact p.Prime] (hm : 0<m) (hb : 1<b)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, (uniformTime (outputSize m) b p K κ n:ℝ)≤(n:ℝ)^ε := by sorry
