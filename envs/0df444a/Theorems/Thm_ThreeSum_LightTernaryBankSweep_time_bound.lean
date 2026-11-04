-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankSweep_time_bound
-- name    : ThreeSum.LightTernaryBankSweep.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:26.231762+00:00
-- url     : https://prove2.me/theorems/d48abcee-b964-47a0-a5d0-393548274927
-- title:
--   Light Ternary Bank Sweep: time bound
-- statement:
--   The Light Ternary Bank Sweep construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L17-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L17-L21

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankSweep

theorem ThreeSum.LightTernaryBankSweep.time_bound (N L n : ℕ) : time N L n≤4000*(N+1)*(N+L+1)*(n+1) := by sorry
