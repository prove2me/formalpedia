-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearPair_pairTime_bound
-- name    : ThreeSum.LightTernaryNearPair.pairTime_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:06:24.821046+00:00
-- url     : https://prove2.me/theorems/7bab281a-10e8-4893-9f24-bb41b2bd1387
-- title:
--   Light Ternary Near Pair: pair Time bound
-- statement:
--   Both actual reconstructions and the product retain the near-row Gibbs
--   exponent; all additional work is polynomial in the word dimension.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearPair.lean#L198-L223
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearPair.lean#L198-L223

import Definitions.Def_Submission_ThreeSum_LightTernaryNearSourceWords
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryNearPair
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

theorem ThreeSum.LightTernaryNearPair.pairTime_bound (N rows : ℕ) (f g : Config) :
    pairTime N rows f g≤23000*
      (N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3)^3*(rows+1) := by sorry
