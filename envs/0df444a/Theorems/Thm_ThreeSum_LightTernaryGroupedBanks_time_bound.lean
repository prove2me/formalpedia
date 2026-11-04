-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryGroupedBanks_time_bound
-- name    : ThreeSum.LightTernaryGroupedBanks.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:49.559244+00:00
-- url     : https://prove2.me/theorems/bfd73b16-908e-4a2f-9b6d-e59fbeed30e5
-- title:
--   Light Ternary Grouped Banks: time bound
-- statement:
--   The Light Ternary Grouped Banks construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupBankResources.lean#L15-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupBankResources.lean#L15-L22

import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedBanks
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankSweep_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedBanks

theorem ThreeSum.LightTernaryGroupedBanks.time_bound (groups N L n : ℕ) :
    time groups N L n≤31000*(groups+1)*(N+1)*(N+L+1)*(n+1) := by sorry
