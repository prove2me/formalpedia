-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_prime_crude_upper
-- name    : ThreeSum.WeightedGlobalCoverScale.prime_crude_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:12.264113+00:00
-- url     : https://prove2.me/theorems/e56cacaa-a352-45a7-bfd0-929cd6543787
-- title:
--   Weighted Global Cover Scale: prime crude upper
-- statement:
--   The Weighted Global Cover Scale construction uses the prime crude upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L77-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L77-L88

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

theorem ThreeSum.WeightedGlobalCoverScale.prime_crude_upper (m : ℕ) : prime m ≤ 2^(2*fixedLength m+2) := by sorry
