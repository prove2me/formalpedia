-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeTensorScore_packed_digits
-- name    : ThreeSum.WeightedGlobalNativeTensorScore.packed_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:06:58.065709+00:00
-- url     : https://prove2.me/theorems/d8eca056-8937-4372-8343-17407e93cda4
-- title:
--   Weighted Global Native Tensor Score: packed digits
-- statement:
--   The actual radix decoder reads the four physical row-major tensor
--   coordinates exactly; no column tuple is supplied as runtime advice.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTensorScore.lean#L27-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTensorScore.lean#L27-L58

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeTensorScore
open TernaryJointType WeightedGlobalNativePairMoments
open LightWeightedGlobalTensorFactory LightTernaryPairedPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000

theorem ThreeSum.WeightedGlobalNativeTensorScore.packed_digits {p a b c d : ℕ} (hp : 0<p)
    (ha : a<p) (hb : b<p) (hc : c<p) (hd : d<p) :
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 0=a ∧
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 1=b ∧
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 2=c ∧
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 3=d := by sorry
