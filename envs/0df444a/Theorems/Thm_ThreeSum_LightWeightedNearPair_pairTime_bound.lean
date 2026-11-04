-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearPair_pairTime_bound
-- name    : ThreeSum.LightWeightedNearPair.pairTime_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:07:15.105349+00:00
-- url     : https://prove2.me/theorems/c40d18ca-4f7a-4b3c-a875-c70957998060
-- title:
--   Light Weighted Near Pair: pair Time bound
-- statement:
--   Both actual reconstructions and the product retain the near-row Gibbs
--   exponent; all additional work is polynomial in the word dimension.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearPair.lean#L207-L232
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearPair.lean#L207-L232

import Definitions.Def_Submission_Weighted_KernelProgram
import Definitions.Def_Submission_Weighted_NearSourceWords
import Definitions.Def_Submission_Weighted_NearPair
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedNearPair
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedNearPair.pairTime_bound (N rows : ℕ) (f g : Config) :
    pairTime N rows f g≤23000*
      (N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3)^3*(rows+1) := by sorry
