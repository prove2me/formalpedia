-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_vertices_upper
-- name    : ThreeSum.TernaryCoverScale.vertices_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:59:20.298897+00:00
-- url     : https://prove2.me/theorems/d8760c5a-c2c0-4392-8515-2482ea728774
-- title:
--   Ternary Cover Scale: vertices upper
-- statement:
--   The Ternary Cover Scale construction uses the vertices upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L66-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L66-L68

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

theorem ThreeSum.TernaryCoverScale.vertices_upper (L : ℕ) (a : DigitType) : (vertices L a).card ≤ 3^L := by sorry
