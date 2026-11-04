-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_column_keeps
-- name    : ThreeSum.LightWeightedEulerMetadata.column_keeps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:22:25.549606+00:00
-- url     : https://prove2.me/theorems/3e3b34a0-f8fd-48a8-a2ec-b7fd88dee750
-- title:
--   Light Weighted Euler Metadata: column keeps
-- statement:
--   The Light Weighted Euler Metadata construction uses the column keeps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EulerMetadata.lean#L31-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EulerMetadata.lean#L31-L39

import Definitions.Def_Submission_Weighted_PredecessorTable
import Definitions.Def_Submission_Weighted_EulerMetadata
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedEulerMetadata.column_keeps {μ ν : ℕ → ℤ} {ws N rows i k : ℕ}
    (hi : i<N) (hk : k<N) (hne : i≠k)
    (H : LightWeightedPredecessorTable.KeptApart μ ν (ws+k) N rows) (j : ℕ) :
    ν (rowAddr ws N i j)=μ (rowAddr ws N i j) := by sorry
