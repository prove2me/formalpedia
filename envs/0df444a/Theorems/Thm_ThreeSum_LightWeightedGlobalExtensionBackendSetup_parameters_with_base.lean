-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalExtensionBackendSetup_parameters_with_base
-- name    : ThreeSum.LightWeightedGlobalExtensionBackendSetup.parameters_with_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:46:10.460538+00:00
-- url     : https://prove2.me/theorems/19957f5f-1af3-4cd4-a3a5-599c896973b6
-- title:
--   Light Weighted Global Extension Backend Setup: parameters with base
-- statement:
--   The Light Weighted Global Extension Backend Setup construction uses the parameters with base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightExtensionBackendSetupBudget.lean#L29-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightExtensionBackendSetupBudget.lean#L29-L34

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

theorem ThreeSum.LightWeightedGlobalExtensionBackendSetup.parameters_with_base (d p q J : ℕ) : d+p+q+J+2 ≤ (p+1)*(q+d+(J+2)+1) := by sorry
