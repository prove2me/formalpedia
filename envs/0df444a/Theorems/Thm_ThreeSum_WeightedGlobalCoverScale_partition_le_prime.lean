-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_partition_le_prime
-- name    : ThreeSum.WeightedGlobalCoverScale.partition_le_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:40.73726+00:00
-- url     : https://prove2.me/theorems/792a2085-60aa-4f33-8ec3-6276503f7031
-- title:
--   Weighted Global Cover Scale: partition le prime
-- statement:
--   The Weighted Global Cover Scale construction uses the partition le prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L40-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L40-L41

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

theorem ThreeSum.WeightedGlobalCoverScale.partition_le_prime (m : ℕ) : 2^(fixedPi m 1)*3^(fixedPi m 2) ≤ prime m := by sorry
