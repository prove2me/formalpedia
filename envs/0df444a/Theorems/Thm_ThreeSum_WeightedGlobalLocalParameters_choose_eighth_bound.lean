-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_choose_eighth_bound
-- name    : ThreeSum.WeightedGlobalLocalParameters.choose_eighth_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:40.284271+00:00
-- url     : https://prove2.me/theorems/edc15c95-a808-468c-a97d-61ff92e57032
-- title:
--   Weighted Global Local Parameters: choose eighth bound
-- statement:
--   Elementary integer Chernoff bound, with no real logarithms.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L32-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L32-L56

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.WeightedGlobalLocalParameters.choose_eighth_bound (m k : ℕ) (hk : k ≤ 8*m) :
    (8*m).choose k ≤ 2^(m+4*k) := by sorry
