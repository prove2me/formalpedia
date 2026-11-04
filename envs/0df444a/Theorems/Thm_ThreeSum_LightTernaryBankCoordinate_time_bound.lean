-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankCoordinate_time_bound
-- name    : ThreeSum.LightTernaryBankCoordinate.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:43.054555+00:00
-- url     : https://prove2.me/theorems/a79607b2-6e07-47c2-9b54-930ee3fd9b9a
-- title:
--   Light Ternary Bank Coordinate: time bound
-- statement:
--   The Light Ternary Bank Coordinate construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L7-L11
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L7-L11

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankCoordinate

theorem ThreeSum.LightTernaryBankCoordinate.time_bound (N L n : ℕ) : time N L n≤3000*(N+L+1)*(n+1) := by sorry
