-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_right
-- name    : ThreeSum.WeightedGlobalNativeBlockPairs.edges_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:31:48.656177+00:00
-- url     : https://prove2.me/theorems/81b818d1-e41f-41ea-af5c-02af8552b67c
-- title:
--   Weighted Global Native Block Pairs: edges right
-- statement:
--   The Weighted Global Native Block Pairs construction uses the edges right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L74-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L74-L75

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

theorem ThreeSum.WeightedGlobalNativeBlockPairs.edges_right (a b : Fin r→{w // w∈vertices L α})
    (q : Fin r→{w // w∈vertices L π}) (h) (i : Fin r) : right (edges a b q h i)=(b i).val := by sorry

attribute [defeq] ThreeSum.WeightedGlobalNativeBlockPairs.edges_right
