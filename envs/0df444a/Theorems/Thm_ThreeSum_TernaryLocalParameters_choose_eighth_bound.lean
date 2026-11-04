-- Prove2me | Theorems.Thm_ThreeSum_TernaryLocalParameters_choose_eighth_bound
-- name    : ThreeSum.TernaryLocalParameters.choose_eighth_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:36.192019+00:00
-- url     : https://prove2.me/theorems/abfb6155-1120-4563-8a09-8790f8598259
-- title:
--   Ternary Local Parameters: choose eighth bound
-- statement:
--   Elementary integer Chernoff bound, with no real logarithms.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L26-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L26-L50

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.TernaryLocalParameters.choose_eighth_bound (m k : ℕ) (hk : k ≤ 8*m) :
    (8*m).choose k ≤ 2^(m+4*k) := by sorry
