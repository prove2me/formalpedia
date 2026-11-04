-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankSweep_time_bound
-- name    : ThreeSum.LightWeightedBankSweep.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:08.760385+00:00
-- url     : https://prove2.me/theorems/dc8b55e6-76a4-43c4-9de6-d07869c719e7
-- title:
--   Light Weighted Bank Sweep: time bound
-- statement:
--   The Light Weighted Bank Sweep construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L22-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L22-L26

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankSweep

theorem ThreeSum.LightWeightedBankSweep.time_bound (N L n : ℕ) : time N L n≤4000*(N+1)*(N+L+1)*(n+1) := by sorry
