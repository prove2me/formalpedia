-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_partition_le_prime
-- name    : ThreeSum.TernaryCoverScale.partition_le_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:59:13.473129+00:00
-- url     : https://prove2.me/theorems/947a613a-1086-4aa2-94b3-e3c65c8f5691
-- title:
--   Ternary Cover Scale: partition le prime
-- statement:
--   The Ternary Cover Scale construction uses the partition le prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L33-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L33-L34

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

theorem ThreeSum.TernaryCoverScale.partition_le_prime (m : ℕ) : 2^(fixedPi m 1)*3^(fixedPi m 2) ≤ prime m := by sorry
