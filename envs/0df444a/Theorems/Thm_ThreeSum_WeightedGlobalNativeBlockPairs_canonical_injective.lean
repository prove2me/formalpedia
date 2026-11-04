-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_canonical_injective
-- name    : ThreeSum.WeightedGlobalNativeBlockPairs.canonical_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:28:35.740563+00:00
-- url     : https://prove2.me/theorems/13cd2961-4091-4ac7-bdc8-59854cc6a462
-- title:
--   Weighted Global Native Block Pairs: canonical injective
-- statement:
--   The Weighted Global Native Block Pairs construction uses the canonical injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L27-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L27-L31

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

theorem ThreeSum.WeightedGlobalNativeBlockPairs.canonical_injective : Function.Injective (@canonical r L) := by sorry
