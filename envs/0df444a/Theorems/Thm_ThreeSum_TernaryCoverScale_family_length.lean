-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_family_length
-- name    : ThreeSum.TernaryCoverScale.family_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:31.092649+00:00
-- url     : https://prove2.me/theorems/72d912b1-55a0-42fd-ac23-d8fcdf81ee73
-- title:
--   Ternary Cover Scale: family length
-- statement:
--   The Ternary Cover Scale construction uses the family length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L62-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L62-L64

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency

theorem ThreeSum.TernaryCoverScale.family_length (m k : ℕ) :
    (family m k).length = frequencyFactor m*(Nat.log2 (prime m^2)+1) := by sorry
