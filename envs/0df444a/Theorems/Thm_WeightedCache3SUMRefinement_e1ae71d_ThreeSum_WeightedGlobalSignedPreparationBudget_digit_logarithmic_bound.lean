-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedPreparationBudget_digit_logarithmic_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPreparationBudget.digit_logarithmic_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:26:02.747846+00:00
-- url     : https://prove2.me/theorems/6fec1814-b339-4e75-a06d-1b5e9d96d86a
-- title:
--   digit_logarithmic_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L45-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L45-L84

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPreparationBudget.digit_logarithmic_bound {m b n U : ℕ} (hm : 0<m) (hb : 1<b) (hn : 1<n)
    {κ : ℝ} (hκ : 0≤κ) (hU : (U : ℝ)≤(n : ℝ)^κ) (hlog : 1≤Real.log (n : ℝ)) :
    (paddedLength b U (radixLength m n) : ℝ)+1≤
      digitConstant m b κ*Real.log (n : ℝ) := by sorry
