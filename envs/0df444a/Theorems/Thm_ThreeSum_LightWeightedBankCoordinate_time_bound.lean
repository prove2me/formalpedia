-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankCoordinate_time_bound
-- name    : ThreeSum.LightWeightedBankCoordinate.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:20.480142+00:00
-- url     : https://prove2.me/theorems/7348a7db-f96a-41e4-a9ab-eed24d640e2a
-- title:
--   Light Weighted Bank Coordinate: time bound
-- statement:
--   The Light Weighted Bank Coordinate construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L12-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L12-L16

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankCoordinate

theorem ThreeSum.LightWeightedBankCoordinate.time_bound (N L n : ℕ) : time N L n≤3000*(N+L+1)*(n+1) := by sorry
