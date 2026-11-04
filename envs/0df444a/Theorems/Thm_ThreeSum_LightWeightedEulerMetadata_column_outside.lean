-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_column_outside
-- name    : ThreeSum.LightWeightedEulerMetadata.column_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:22:03.43053+00:00
-- url     : https://prove2.me/theorems/96d5275b-d042-445e-a292-2ca1be24531c
-- title:
--   Light Weighted Euler Metadata: column outside
-- statement:
--   The Light Weighted Euler Metadata construction uses the column outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EulerMetadata.lean#L41-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EulerMetadata.lean#L41-L50

import Definitions.Def_Submission_Weighted_PredecessorTable
import Definitions.Def_Submission_Weighted_EulerMetadata
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedEulerMetadata.column_outside {μ ν : ℕ → ℤ} {ws N rows k : ℕ} (hk : k<N)
    (H : LightWeightedPredecessorTable.KeptApart μ ν (ws+k) N rows) :
    SameOutside μ ν ws (2*N*rows) := by sorry
