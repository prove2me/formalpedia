-- Prove2me | Theorems.Thm_ThreeSum_TrimScales_localBucketCap_ge_load
-- name    : ThreeSum.TrimScales.localBucketCap_ge_load
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:13:38.713296+00:00
-- url     : https://prove2.me/theorems/bbb32744-486b-4611-b06a-42ecc7bb2500
-- title:
--   Trim Scales: local Bucket Cap ge load
-- statement:
--   The Trim Scales construction uses the local Bucket Cap ge load property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L102-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L102-L112

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.TrimScales.localBucketCap_ge_load (h : ℕ) :
    vertexLoad h ≤ (LocalCoverBounds.localBucketCap h : ℝ) := by sorry
