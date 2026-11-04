-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_writeRecord_kept
-- name    : ThreeSum.LightTernaryPredecessorTable.writeRecord_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:59.057755+00:00
-- url     : https://prove2.me/theorems/46755865-1e18-44ef-be4b-30cff47c90c2
-- title:
--   Light Ternary Predecessor Table: write Record kept
-- statement:
--   The Light Ternary Predecessor Table construction uses the write Record kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessorTable.lean#L41-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessorTable.lean#L41-L45

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem ThreeSum.LightTernaryPredecessorTable.writeRecord_kept {μ : ℕ → ℤ} {dst stride n j : ℕ} {w k : ℤ} (hj : j<n) :
    KeptApart μ (writeRecord μ dst stride n j w k) dst stride n := by sorry
