-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentChannels_initialized_weight_gather
-- name    : ThreeSum.LightTernaryMomentChannels.initialized_weight_gather
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:54.585608+00:00
-- url     : https://prove2.me/theorems/301b93ba-345b-4512-8479-86573535cd23
-- title:
--   Light Ternary Moment Channels: initialized weight gather
-- statement:
--   Original-position gathering in the weighted bank reads initialized
--   weights, including repeated source-word occurrences.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L52-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L52-L58

import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannels
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryMomentChannels.initialized_weight_gather {μ : ℕ→ℤ} {dst originalCount count : ℕ}
    (weight : ℕ→ℤ) (originalPosition : ℕ→ℕ)
    (hinit : ∀ i<originalCount, μ (dst+i)=weight i)
    (hpos : ∀ i<count, originalPosition i<originalCount) :
    ∀ i<count, μ (dst+originalPosition i)=weight (originalPosition i) := by sorry
