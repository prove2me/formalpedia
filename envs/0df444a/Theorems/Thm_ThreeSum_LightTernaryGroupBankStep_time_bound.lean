-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryGroupBankStep_time_bound
-- name    : ThreeSum.LightTernaryGroupBankStep.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:01.073993+00:00
-- url     : https://prove2.me/theorems/4aeb5289-d545-4c0d-8081-2027a5e9c69a
-- title:
--   Light Ternary Group Bank Step: time bound
-- statement:
--   The Light Ternary Group Bank Step construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupBankResources.lean#L5-L10
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupBankResources.lean#L5-L10

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
open ThreeSum ThreeSum.LightTernaryGroupBankStep

theorem ThreeSum.LightTernaryGroupBankStep.time_bound (N L n : ℕ) : time N L n≤30000*(N+1)*(N+L+1)*(n+1) := by sorry
