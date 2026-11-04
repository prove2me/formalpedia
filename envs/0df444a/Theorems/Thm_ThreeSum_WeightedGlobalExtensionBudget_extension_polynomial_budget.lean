-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalExtensionBudget_extension_polynomial_budget
-- name    : ThreeSum.WeightedGlobalExtensionBudget.extension_polynomial_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:33:35.806516+00:00
-- url     : https://prove2.me/theorems/99e32083-d4bc-4ba0-b050-3539d9ee24bf
-- title:
--   Weighted Global Extension Budget: extension polynomial budget
-- statement:
--   Every fixed polynomial cost of constructing the field, its complete
--   multiplication table, and every seed row is absorbed into any positive power
--   of the original input length. The field size is the actual ceiling-log size.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExtensionBudget.lean#L41-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExtensionBudget.lean#L41-L65

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalExtensionBudget
open ThreeSum.TernaryExtensionEncoding
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalSignedPreparationBudget
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalExtensionBudget.extension_polynomial_budget {m b : ℕ} (hm : 0<m) (hb : 1<b)
    {κ ε : ℝ} (hκ : 0≤κ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) (D K : ℕ)
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      let J := paddedLength b (U n) (radixLength m n)
      A*((p^(menuDegree p (J+2) K)+menuDegree p (J+2) K+(J+2)+1 : ℕ) : ℝ)^D≤
        (n : ℝ)^ε := by sorry
