-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_localWeights_eq_range
-- name    : ThreeSum.WeightEnumeration.localWeights_eq_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:41.025246+00:00
-- url     : https://prove2.me/theorems/7dc18c44-2d8b-47f9-8581-1564840afded
-- title:
--   Weight Enumeration: local Weights eq range
-- statement:
--   The Weight Enumeration construction uses the local Weights eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L190-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L190-L194

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]

theorem ThreeSum.WeightEnumeration.localWeights_eq_range (h : ℕ) :
    allWeights (512*h) (localValues h) =
      (List.range ((LocalCoverBounds.localPrime h)^(2*(512*h)))).map
        (decodedWeight (K := LocalField h) (512*h) (LocalCoverBounds.localPrime h)) := by sorry
