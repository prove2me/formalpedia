-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_vertices_upper
-- name    : ThreeSum.WeightedGlobalCoverScale.vertices_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:16.574879+00:00
-- url     : https://prove2.me/theorems/3dc6d703-ff70-43bb-9ee6-89dd7c819537
-- title:
--   Weighted Global Cover Scale: vertices upper
-- statement:
--   The Weighted Global Cover Scale construction uses the vertices upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L73-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L73-L75

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

theorem ThreeSum.WeightedGlobalCoverScale.vertices_upper (L : ℕ) (a : DigitType) : (vertices L a).card ≤ 3^L := by sorry
