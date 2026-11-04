-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_time_bound
-- name    : ThreeSum.LightWeightedGroupBankStep.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:16.118054+00:00
-- url     : https://prove2.me/theorems/da6d7ee6-9712-4144-902a-ed4913b1a2d5
-- title:
--   Light Weighted Group Bank Step: time bound
-- statement:
--   The Light Weighted Group Bank Step construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupBankResources.lean#L10-L15
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupBankResources.lean#L10-L15

import Definitions.Def_Submission_Weighted_GroupedBanks
import Definitions.Def_Submission_Weighted_GroupBankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankSweep_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGroupBankStep

theorem ThreeSum.LightWeightedGroupBankStep.time_bound (N L n : ℕ) : time N L n≤30000*(N+1)*(N+L+1)*(n+1) := by sorry
