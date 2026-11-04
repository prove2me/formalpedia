-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalExtensionBackendSetup_time_eventually
-- name    : ThreeSum.LightWeightedGlobalExtensionBackendSetup.time_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:54:40.437492+00:00
-- url     : https://prove2.me/theorems/20865c30-8796-40ac-815b-250d80e72ca9
-- title:
--   Light Weighted Global Extension Backend Setup: time eventually
-- statement:
--   The Light Weighted Global Extension Backend Setup construction uses the time eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightExtensionBackendSetupBudget.lean#L59-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightExtensionBackendSetupBudget.lean#L59-L74

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

theorem ThreeSum.LightWeightedGlobalExtensionBackendSetup.time_eventually {m b : ℕ} (hm : 0 < m) (hb : 1 < b)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (K : ℕ) (U base : ℕ → ℕ)
    (hU : ∀ n, 1 < n → (U n : ℝ) ≤ (n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      let J := paddedLength b (U n) (radixLength m n)
      let d := menuDegree p (J+2) K
      (time (base n) d p (p^d) J : ℝ) ≤ (n : ℝ)^ε := by sorry
