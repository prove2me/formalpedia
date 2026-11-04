-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedPreparationBudget_digit_logarithmic_bound
-- name    : ThreeSum.WeightedGlobalSignedPreparationBudget.digit_logarithmic_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:29:15.854241+00:00
-- url     : https://prove2.me/theorems/bc293c23-581a-4972-89cf-afac8723434a
-- title:
--   Weighted Global Signed Preparation Budget: digit logarithmic bound
-- statement:
--   The Weighted Global Signed Preparation Budget construction uses the digit logarithmic bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L45-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L45-L84

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

theorem ThreeSum.WeightedGlobalSignedPreparationBudget.digit_logarithmic_bound {m b n U : ℕ} (hm : 0<m) (hb : 1<b) (hn : 1<n)
    {κ : ℝ} (hκ : 0≤κ) (hU : (U : ℝ)≤(n : ℝ)^κ) (hlog : 1≤Real.log (n : ℝ)) :
    (paddedLength b U (radixLength m n) : ℝ)+1≤
      digitConstant m b κ*Real.log (n : ℝ) := by sorry
