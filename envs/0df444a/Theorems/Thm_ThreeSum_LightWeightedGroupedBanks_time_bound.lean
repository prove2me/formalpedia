-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_time_bound
-- name    : ThreeSum.LightWeightedGroupedBanks.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:18.212129+00:00
-- url     : https://prove2.me/theorems/b933a18b-8919-4606-ab64-d5a3175cdfa2
-- title:
--   Light Weighted Grouped Banks: time bound
-- statement:
--   The Light Weighted Grouped Banks construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupBankResources.lean#L20-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupBankResources.lean#L20-L27

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
open ThreeSum ThreeSum.LightWeightedGroupedBanks

theorem ThreeSum.LightWeightedGroupedBanks.time_bound (groups N L n : ℕ) :
    time groups N L n≤31000*(groups+1)*(N+1)*(N+L+1)*(n+1) := by sorry
