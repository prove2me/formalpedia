-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedPreparationBudget_carry_preparation_budget
-- name    : ThreeSum.WeightedGlobalSignedPreparationBudget.carry_preparation_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:29:33.020062+00:00
-- url     : https://prove2.me/theorems/ec79caa2-c77b-468f-bee3-1e24f7f58b24
-- title:
--   Weighted Global Signed Preparation Budget: carry preparation budget
-- statement:
--   This includes even the crude requester-by-carry product preprocessing.
--   The physical matrix/table/pass theorems discharge its per-iteration costs.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L145-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L145-L166

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

theorem ThreeSum.WeightedGlobalSignedPreparationBudget.carry_preparation_budget {m b : ℕ} (hm : 0<m) (hb : 1<b)
    {κ δ ε : ℝ} (hκ : 0≤κ) (hδ : carryExponent m b κ<δ) (hε : 0<ε)
    (A : ℝ) (hA : 0≤A) (d : ℕ) (U : ℕ→ℕ)
    (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      A*(n : ℝ)*(2 : ℝ)^paddedLength b (U n) (radixLength m n)*
        ((paddedLength b (U n) (radixLength m n) : ℝ)+1)^d*
        ((Nat.log 2 (3*U n+1) : ℝ)+2)^d≤(n : ℝ)^(1+δ+ε) := by sorry
