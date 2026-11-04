-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_keptApart_refl
-- name    : ThreeSum.LightWeightedPredecessorTable.keptApart_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:39.345259+00:00
-- url     : https://prove2.me/theorems/81eaf6f0-3af8-488b-830c-e1bcb1917897
-- title:
--   Light Weighted Predecessor Table: kept Apart refl
-- statement:
--   The Light Weighted Predecessor Table construction uses the kept Apart refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L43-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PredecessorTable.lean#L43-L44

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedPredecessorTable.keptApart_refl (μ : ℕ → ℤ) (dst stride n : ℕ) : KeptApart μ μ dst stride n := by sorry
