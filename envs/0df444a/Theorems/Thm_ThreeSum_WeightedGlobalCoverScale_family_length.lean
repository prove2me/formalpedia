-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_family_length
-- name    : ThreeSum.WeightedGlobalCoverScale.family_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:01.872804+00:00
-- url     : https://prove2.me/theorems/ade8b993-2244-4610-9e7c-e6dabdbc2c99
-- title:
--   Weighted Global Cover Scale: family length
-- statement:
--   The Weighted Global Cover Scale construction uses the family length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L69-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L69-L71

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

theorem ThreeSum.WeightedGlobalCoverScale.family_length (m k : ℕ) :
    (family m k).length = frequencyFactor m*(Nat.log2 (prime m^2)+1) := by sorry
