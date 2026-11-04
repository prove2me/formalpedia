-- Prove2me | Theorems.Thm_ThreeSum_LightSortedBands_family_covers
-- name    : ThreeSum.LightSortedBands.family_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:38.273557+00:00
-- url     : https://prove2.me/theorems/4d7b21c6-bf99-4a91-a663-b0e78dd631a9
-- title:
--   Light Sorted Bands: family covers
-- statement:
--   Membership witnesses from the original class lie in an emitted band.
--   Thus deduplication does not lose an original-position witness.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean#L226-L234
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean#L226-L234

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_LightSortedBands
set_option autoImplicit false
open ThreeSum ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSortedBands.family_covers {L original : List ℤ} {g : ℕ} (hg : 0 < g)
    (hs : L.Pairwise (· < ·)) (hmem : ∀ z, z ∈ L ↔ z ∈ original)
    {z : ℤ} (hz : z ∈ original) :
    let A := BandPartition.family (fun i => L.getD i 0) L.length g hg (getD_strict hs)
    ∃ i < A.size, A.lower i ≤ z ∧ z ≤ A.upper i := by sorry
