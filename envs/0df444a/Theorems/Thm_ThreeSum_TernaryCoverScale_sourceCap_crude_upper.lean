-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_sourceCap_crude_upper
-- name    : ThreeSum.TernaryCoverScale.sourceCap_crude_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:27.413997+00:00
-- url     : https://prove2.me/theorems/0ad9f411-c57b-4903-85b5-25f10471f92e
-- title:
--   Ternary Cover Scale: source Cap crude upper
-- statement:
--   The Ternary Cover Scale construction uses the source Cap crude upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L83-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L83-L96

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

theorem ThreeSum.TernaryCoverScale.sourceCap_crude_upper (m : ℕ) : sourceCap m (prime m) ≤ 2^(2*fixedLength m+4) := by sorry
