-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_column_outside
-- name    : ThreeSum.LightTernaryEulerMetadata.column_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:30:06.392663+00:00
-- url     : https://prove2.me/theorems/e0816e04-609f-42fa-8f9e-22d3a7c9e1c5
-- title:
--   Light Ternary Euler Metadata: column outside
-- statement:
--   The Light Ternary Euler Metadata construction uses the column outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean#L36-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEulerMetadata.lean#L36-L45

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem ThreeSum.LightTernaryEulerMetadata.column_outside {μ ν : ℕ → ℤ} {ws N rows k : ℕ} (hk : k<N)
    (H : LightTernaryPredecessorTable.KeptApart μ ν (ws+k) N rows) :
    SameOutside μ ν ws (2*N*rows) := by sorry
