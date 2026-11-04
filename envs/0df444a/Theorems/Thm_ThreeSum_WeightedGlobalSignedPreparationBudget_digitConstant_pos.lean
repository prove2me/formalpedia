-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalSignedPreparationBudget_digitConstant_pos
-- name    : ThreeSum.WeightedGlobalSignedPreparationBudget.digitConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:29:03.670387+00:00
-- url     : https://prove2.me/theorems/c2a5cbb7-66ac-42f4-ae39-d8355c851b6e
-- title:
--   Weighted Global Signed Preparation Budget: digit Constant pos
-- statement:
--   The Weighted Global Signed Preparation Budget construction uses the digit Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L33-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySignedPreparationBudget.lean#L33-L39

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

theorem ThreeSum.WeightedGlobalSignedPreparationBudget.digitConstant_pos {m b : ℕ} (hm : 0<m) (hb : 1<b) {κ : ℝ} (hκ : 0≤κ) :
    0<digitConstant m b κ := by sorry
