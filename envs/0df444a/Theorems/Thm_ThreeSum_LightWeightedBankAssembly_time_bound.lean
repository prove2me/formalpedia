-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankAssembly_time_bound
-- name    : ThreeSum.LightWeightedBankAssembly.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:04.032139+00:00
-- url     : https://prove2.me/theorems/71821947-a35f-42e5-a5ad-6a467cc0d2b3
-- title:
--   Light Weighted Bank Assembly: time bound
-- statement:
--   The Light Weighted Bank Assembly construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L32-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L32-L38

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly

theorem ThreeSum.LightWeightedBankAssembly.time_bound (N L n : ℕ) : time N L n≤20000*(N+1)*(N+L+1)*(n+1) := by sorry
