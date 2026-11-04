-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_capExponent_mul_upper
-- name    : ThreeSum.WeightedGlobalCoverScale.capExponent_mul_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:26.198874+00:00
-- url     : https://prove2.me/theorems/7465eb92-36a1-4138-9d04-42837cd420ba
-- title:
--   Weighted Global Cover Scale: cap Exponent mul upper
-- statement:
--   The Weighted Global Cover Scale construction uses the cap Exponent mul upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L116-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L116-L123

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency

theorem ThreeSum.WeightedGlobalCoverScale.capExponent_mul_upper (m k : ℕ) :
    k*capExponent (prime m) (sourceCap m (prime m)) k ≤ 12*fixedLength m+8*k^2+26+k := by sorry
