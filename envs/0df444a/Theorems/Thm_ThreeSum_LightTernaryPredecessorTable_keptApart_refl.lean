-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_keptApart_refl
-- name    : ThreeSum.LightTernaryPredecessorTable.keptApart_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:57.76961+00:00
-- url     : https://prove2.me/theorems/0b433ece-2cb4-4ce2-819c-2c9b2a4fbb5b
-- title:
--   Light Ternary Predecessor Table: kept Apart refl
-- statement:
--   The Light Ternary Predecessor Table construction uses the kept Apart refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessorTable.lean#L38-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessorTable.lean#L38-L39

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem ThreeSum.LightTernaryPredecessorTable.keptApart_refl (μ : ℕ → ℤ) (dst stride n : ℕ) : KeptApart μ μ dst stride n := by sorry
