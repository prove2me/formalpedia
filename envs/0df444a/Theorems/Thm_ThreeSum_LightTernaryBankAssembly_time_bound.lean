-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankAssembly_time_bound
-- name    : ThreeSum.LightTernaryBankAssembly.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:07.426572+00:00
-- url     : https://prove2.me/theorems/798de3d5-7eca-4603-8c12-974a153f88df
-- title:
--   Light Ternary Bank Assembly: time bound
-- statement:
--   The Light Ternary Bank Assembly construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L27-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L27-L33

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly

theorem ThreeSum.LightTernaryBankAssembly.time_bound (N L n : ℕ) : time N L n≤20000*(N+1)*(N+L+1)*(n+1) := by sorry
