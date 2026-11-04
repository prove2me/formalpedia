-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativePairMoments_channel_sum
-- name    : ThreeSum.WeightedGlobalNativePairMoments.channel_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:57:20.575528+00:00
-- url     : https://prove2.me/theorems/3b8e5269-46e0-43df-9286-37a3906468f3
-- title:
--   Weighted Global Native Pair Moments: channel sum
-- statement:
--   The binomial channel sum is exactly the positive physical moment,
--   including the query word's common, positive factorial factor.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairMoments.lean#L49-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairMoments.lean#L49-L73

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentChannelFactory
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePairMoments
open Finset TernaryJointType
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativePairMoments.channel_sum {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (k i : ℕ) :
    (∑ j∈range (k+1), LightWeightedGlobalMomentChannelFactory.score S B C k j i)=
      ∑ p : Pair S i, mass S i p*mode B C p^k := by sorry
