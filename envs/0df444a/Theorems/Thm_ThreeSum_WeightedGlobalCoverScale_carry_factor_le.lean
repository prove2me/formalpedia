-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_carry_factor_le
-- name    : ThreeSum.WeightedGlobalCoverScale.carry_factor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:23.109197+00:00
-- url     : https://prove2.me/theorems/92dc3603-ce54-4146-b910-7073e997052b
-- title:
--   Weighted Global Cover Scale: carry factor le
-- statement:
--   The Weighted Global Cover Scale construction uses the carry factor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L318-L323
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L318-L323

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

theorem ThreeSum.WeightedGlobalCoverScale.carry_factor_le (C c d b : ℕ)
    (hb : b ≤ c*(fixedLength (scale C c d)+1)^d) :
    b*(family (scale C c d) (momentOrder C)).length*
      rawThreshold (prime (scale C c d)) (sourceCap (scale C c d) (prime (scale C c d)))
        (momentOrder C) ≤ localFactor C c d := by sorry
