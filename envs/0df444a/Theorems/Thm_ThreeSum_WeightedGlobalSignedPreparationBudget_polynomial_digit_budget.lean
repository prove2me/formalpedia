-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedPreparationBudget_polynomial_digit_budget
-- name    : ThreeSum.WeightedGlobalSignedPreparationBudget.polynomial_digit_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:24:10.860223+00:00
-- url     : https://prove2.me/theorems/50207ec8-b5dd-4690-b40c-bff2ebe490b5
-- title:
--   Weighted Global Signed Preparation Budget: polynomial digit budget
-- statement:
--   The Weighted Global Signed Preparation Budget construction uses the polynomial digit budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L107-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L107-L141

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedPreparationBudget
open Filter Real Asymptotics WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalLocalParameters WeightedGlobalParameters
open scoped Topology

theorem ThreeSum.WeightedGlobalSignedPreparationBudget.polynomial_digit_budget {m b : ℕ} (hm : 0<m) (hb : 1<b)
    {κ ε : ℝ} (hκ : 0≤κ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) (d : ℕ)
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      A*((paddedLength b (U n) (radixLength m n) : ℝ)+1)^d*
        ((Nat.log 2 (3*U n+1) : ℝ)+2)^d≤(n : ℝ)^ε := by sorry
