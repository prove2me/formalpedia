-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_occurrenceCode_injective
-- name    : ThreeSum.WeightedGlobalNativeBlockPairs.occurrenceCode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:31:57.168364+00:00
-- url     : https://prove2.me/theorems/94a10ce4-7831-499b-9d95-32f8e693f365
-- title:
--   Weighted Global Native Block Pairs: occurrence Code injective
-- statement:
--   The physical same-map bank code retains every local map occurrence.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L37-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L37-L59

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalTupleRecords
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeBlockPairs
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalRepeatedWords
attribute [local instance] Classical.propDecidable
variable {r L F : ℕ} {α π : DigitType}

theorem ThreeSum.WeightedGlobalNativeBlockPairs.occurrenceCode_injective : Function.Injective (@occurrenceCode r F) := by sorry
