-- Prove2me | Theorems.Thm_ThreeSum_LightSortedBands_family_bounded
-- name    : ThreeSum.LightSortedBands.family_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:26.211394+00:00
-- url     : https://prove2.me/theorems/7805e4be-bcf1-4039-bb12-4d23d67ec30e
-- title:
--   Light Sorted Bands: family bounded
-- statement:
--   The Light Sorted Bands construction uses the family bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean#L213-L222
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean#L213-L222

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

theorem ThreeSum.LightSortedBands.family_bounded {L original : List ℤ} {g U : ℕ} (hg : 0 < g)
    (hs : L.Pairwise (· < ·)) (hmem : ∀ z, z ∈ L ↔ z ∈ original)
    (hU : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    LightBandEnumeration.Bounded
      (BandPartition.family (fun i => L.getD i 0) L.length g hg (getD_strict hs)) U := by sorry
