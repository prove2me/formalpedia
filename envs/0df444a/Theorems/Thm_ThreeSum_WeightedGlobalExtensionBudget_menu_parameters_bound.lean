-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalExtensionBudget_menu_parameters_bound
-- name    : ThreeSum.WeightedGlobalExtensionBudget.menu_parameters_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:33:58.857209+00:00
-- url     : https://prove2.me/theorems/5ff81827-3ca0-4445-bdf0-98caed83679a
-- title:
--   Weighted Global Extension Budget: menu parameters bound
-- statement:
--   The Weighted Global Extension Budget construction uses the menu parameters bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExtensionBudget.lean#L28-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryExtensionBudget.lean#L28-L36

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

theorem ThreeSum.WeightedGlobalExtensionBudget.menu_parameters_bound (J K : ℕ) :
    p^(menuDegree p (J+2) K)+menuDegree p (J+2) K+(J+2)+1≤
      (48*p^(4*K+1)+3)*(J+1) := by sorry
