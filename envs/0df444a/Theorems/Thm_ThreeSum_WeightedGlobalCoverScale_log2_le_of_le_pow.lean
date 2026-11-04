-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_log2_le_of_le_pow
-- name    : ThreeSum.WeightedGlobalCoverScale.log2_le_of_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:35:50.821186+00:00
-- url     : https://prove2.me/theorems/94e0d9a4-0d7b-4eee-bf52-262b6129e7cd
-- title:
--   Weighted Global Cover Scale: log2 le of le pow
-- statement:
--   The Weighted Global Cover Scale construction uses the log2 le of le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L105-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L105-L107

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

theorem ThreeSum.WeightedGlobalCoverScale.log2_le_of_le_pow {x e : ℕ} (h : x ≤ 2^e) : Nat.log2 x ≤ e := by sorry
