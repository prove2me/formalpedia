-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_prime_gt_four
-- name    : ThreeSum.WeightedGlobalCoverScale.prime_gt_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:01.662306+00:00
-- url     : https://prove2.me/theorems/14799105-376f-4ecf-99a7-2cd3df79abad
-- title:
--   Weighted Global Cover Scale: prime gt four
-- statement:
--   The Weighted Global Cover Scale construction uses the prime gt four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L43-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L43-L50

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

theorem ThreeSum.WeightedGlobalCoverScale.prime_gt_four {m : ℕ} (hm : 0 < m) : 4 < prime m := by sorry
