-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalExtensionBackendSetup_reserve_eventually
-- name    : ThreeSum.LightWeightedGlobalExtensionBackendSetup.reserve_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:54:26.464086+00:00
-- url     : https://prove2.me/theorems/4fdea628-6b4b-4bce-a631-12970031507a
-- title:
--   Light Weighted Global Extension Backend Setup: reserve eventually
-- statement:
--   The Light Weighted Global Extension Backend Setup construction uses the reserve eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightExtensionBackendSetupBudget.lean#L76-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightExtensionBackendSetupBudget.lean#L76-L85

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightExtensionBackendSetup
import Definitions.Def_Submission_ThreeSum_LightExtensionBackendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_LightExtensionBackendSetupBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalExtensionBackendSetup
open LightExtensionBackendLayout TernaryExtensionEncoding WeightedGlobalSignedPadding WeightedGlobalCoverScale Filter Real
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.LightWeightedGlobalExtensionBackendSetup.reserve_eventually {m b : ℕ} (hm : 0 < m) (hb : 1 < b)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (K : ℕ) (U : ℕ → ℕ)
    (hU : ∀ n, 1 < n → (U n : ℝ) ≤ (n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      let J := paddedLength b (U n) (radixLength m n)
      let d := menuDegree p (J+2) K
      (reserve d p (p^d) J : ℝ) ≤ (n : ℝ)^ε := by sorry
