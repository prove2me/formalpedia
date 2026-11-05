-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedPreparationBudget_carry_preparation_budget
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPreparationBudget.carry_preparation_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:25:23.8582+00:00
-- url     : https://prove2.me/theorems/03bbd324-c959-408d-a6bd-bdd6d1d19be0
-- title:
--   carry_preparation_budget
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L145-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L145-L166

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryApply
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPreparationBudget
open Filter Real Asymptotics WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalLocalParameters WeightedGlobalParameters
open scoped Topology

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPreparationBudget.carry_preparation_budget {m b : ℕ} (hm : 0<m) (hb : 1<b)
    {κ δ ε : ℝ} (hκ : 0≤κ) (hδ : carryExponent m b κ<δ) (hε : 0<ε)
    (A : ℝ) (hA : 0≤A) (d : ℕ) (U : ℕ→ℕ)
    (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      A*(n : ℝ)*(2 : ℝ)^paddedLength b (U n) (radixLength m n)*
        ((paddedLength b (U n) (radixLength m n) : ℝ)+1)^d*
        ((Nat.log 2 (3*U n+1) : ℝ)+2)^d≤(n : ℝ)^(1+δ+ε) := by sorry
