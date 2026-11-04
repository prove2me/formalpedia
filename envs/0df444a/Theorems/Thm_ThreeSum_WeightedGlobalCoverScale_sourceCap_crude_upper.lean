-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_sourceCap_crude_upper
-- name    : ThreeSum.WeightedGlobalCoverScale.sourceCap_crude_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:52.704436+00:00
-- url     : https://prove2.me/theorems/9cb05874-abe2-47f5-b6a9-bd9947efb150
-- title:
--   Weighted Global Cover Scale: source Cap crude upper
-- statement:
--   The Weighted Global Cover Scale construction uses the source Cap crude upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L90-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L90-L103

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

theorem ThreeSum.WeightedGlobalCoverScale.sourceCap_crude_upper (m : ℕ) : sourceCap m (prime m) ≤ 2^(2*fixedLength m+4) := by sorry
