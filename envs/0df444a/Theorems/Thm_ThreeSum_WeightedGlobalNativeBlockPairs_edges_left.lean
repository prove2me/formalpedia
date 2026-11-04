-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeBlockPairs_edges_left
-- name    : ThreeSum.WeightedGlobalNativeBlockPairs.edges_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:29:17.723491+00:00
-- url     : https://prove2.me/theorems/b463ec09-8168-4e28-95b2-ca35d9e6a85c
-- title:
--   Weighted Global Native Block Pairs: edges left
-- statement:
--   The Weighted Global Native Block Pairs construction uses the edges left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L72-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeBlockPairs.lean#L72-L73

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

theorem ThreeSum.WeightedGlobalNativeBlockPairs.edges_left (a b : Fin r→{w // w∈vertices L α})
    (q : Fin r→{w // w∈vertices L π}) (h) (i : Fin r) : left (edges a b q h i)=(a i).val := by sorry

attribute [defeq] ThreeSum.WeightedGlobalNativeBlockPairs.edges_left
