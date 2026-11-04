-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_rowAddr_ne
-- name    : ThreeSum.LightWeightedEulerMetadata.rowAddr_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:22:29.840199+00:00
-- url     : https://prove2.me/theorems/2ca68612-3a5c-470f-9ac9-e9bacf196ee4
-- title:
--   Light Weighted Euler Metadata: row Addr ne
-- statement:
--   The Light Weighted Euler Metadata construction uses the row Addr ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EulerMetadata.lean#L22-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EulerMetadata.lean#L22-L29

import Definitions.Def_Submission_Weighted_PredecessorTable
import Definitions.Def_Submission_Weighted_EulerMetadata
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEulerMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedEulerMetadata.rowAddr_ne {ws N i k j l : ℕ} (hi : i<N) (hk : k<N) (hne : i≠k) :
    rowAddr ws N i j≠rowAddr ws N k l := by sorry
