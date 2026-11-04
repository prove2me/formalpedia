-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_column_keeps
-- name    : ThreeSum.LightTernaryEulerMetadata.column_keeps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:30:03.681948+00:00
-- url     : https://prove2.me/theorems/1bc6f1dd-56d8-4063-b1a7-6f0f7cec9225
-- title:
--   Light Ternary Euler Metadata: column keeps
-- statement:
--   The Light Ternary Euler Metadata construction uses the column keeps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean#L26-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean#L26-L34

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem ThreeSum.LightTernaryEulerMetadata.column_keeps {μ ν : ℕ → ℤ} {ws N rows i k : ℕ}
    (hi : i<N) (hk : k<N) (hne : i≠k)
    (H : LightTernaryPredecessorTable.KeptApart μ ν (ws+k) N rows) (j : ℕ) :
    ν (rowAddr ws N i j)=μ (rowAddr ws N i j) := by sorry
