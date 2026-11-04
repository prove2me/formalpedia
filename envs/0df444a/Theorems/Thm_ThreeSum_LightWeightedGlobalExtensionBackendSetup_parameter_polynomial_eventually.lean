-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalExtensionBackendSetup_parameter_polynomial_eventually
-- name    : ThreeSum.LightWeightedGlobalExtensionBackendSetup.parameter_polynomial_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:43:20.089427+00:00
-- url     : https://prove2.me/theorems/cabe5940-6560-4786-b057-da244a3ba84e
-- title:
--   Light Weighted Global Extension Backend Setup: parameter polynomial eventually
-- statement:
--   Fixed polynomial overhead of the fully concrete field backend is subpolynomial in n.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightExtensionBackendSetupBudget.lean#L39-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightExtensionBackendSetupBudget.lean#L39-L57

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

theorem ThreeSum.LightWeightedGlobalExtensionBackendSetup.parameter_polynomial_eventually {m b : ℕ} (hm : 0 < m) (hb : 1 < b)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (A : ℝ) (hA : 0 ≤ A) (D K : ℕ)
    (U : ℕ → ℕ) (hU : ∀ n, 1 < n → (U n : ℝ) ≤ (n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      let J := paddedLength b (U n) (radixLength m n)
      let d := menuDegree p (J+2) K
      A*((d+p+p^d+J+2 : ℕ) : ℝ)^D ≤ (n : ℝ)^ε := by sorry
