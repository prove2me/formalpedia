-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativePairMoments_support_eq
-- name    : ThreeSum.WeightedGlobalNativePairMoments.support_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:58:41.115926+00:00
-- url     : https://prove2.me/theorems/e8a2fe87-c46c-49ab-8277-f9201dab7959
-- title:
--   Weighted Global Native Pair Moments: support eq
-- statement:
--   The support convention in the paired-rank cap is exactly the support
--   consumed by the physical moment detector.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairMoments.lean#L77-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairMoments.lean#L77-L78

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

theorem ThreeSum.WeightedGlobalNativePairMoments.support_eq {P : Type*} [Fintype P] (mode : P→ℤ) :
    TernaryPhysicalMomentSupport.support mode=TernaryPairedSupport.physicalSupport mode := by sorry
