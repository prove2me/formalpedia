-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedPreparationBudget_binary_logarithmic_bound
-- name    : ThreeSum.WeightedGlobalSignedPreparationBudget.binary_logarithmic_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:27:04.652729+00:00
-- url     : https://prove2.me/theorems/d3a46f27-f8e0-492a-b08f-097d1da3fdf3
-- title:
--   Weighted Global Signed Preparation Budget: binary logarithmic bound
-- statement:
--   The Weighted Global Signed Preparation Budget construction uses the binary logarithmic bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L86-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L86-L105

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

theorem ThreeSum.WeightedGlobalSignedPreparationBudget.binary_logarithmic_bound {n U : ℕ} (hn : 1<n) {κ : ℝ} (hκ : 0≤κ)
    (hU : (U : ℝ)≤(n : ℝ)^κ) (hlog : 1≤Real.log (n : ℝ)) :
    (Nat.log 2 (3*U+1) : ℝ)+2≤binaryConstant κ*Real.log (n : ℝ) := by sorry
