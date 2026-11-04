-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_output
-- name    : ThreeSum.WeightedGlobalNativeBlockPairs.edges_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:29:09.251999+00:00
-- url     : https://prove2.me/theorems/ab40131c-229f-48b2-a1ea-df1943d5afc5
-- title:
--   Weighted Global Native Block Pairs: edges output
-- statement:
--   The Weighted Global Native Block Pairs construction uses the edges output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L76-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L76-L77

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

theorem ThreeSum.WeightedGlobalNativeBlockPairs.edges_output (a b : Fin r→{w // w∈vertices L α})
    (q : Fin r→{w // w∈vertices L π}) (h) (i : Fin r) : output (edges a b q h i)=(q i).val := by sorry

attribute [defeq] ThreeSum.WeightedGlobalNativeBlockPairs.edges_output
