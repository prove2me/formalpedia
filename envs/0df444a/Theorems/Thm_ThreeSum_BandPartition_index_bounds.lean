-- Prove2me | Theorems.Thm_ThreeSum_BandPartition_index_bounds
-- name    : ThreeSum.BandPartition.index_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:33.657014+00:00
-- url     : https://prove2.me/theorems/6d1cdfdb-55f9-4c77-a7aa-db7ff0f1c2fa
-- title:
--   Band Partition: index bounds
-- statement:
--   The Band Partition construction uses the index bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPartition.lean#L76-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPartition.lean#L76-L85

import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_BandPartition
set_option autoImplicit false
open ThreeSum ThreeSum.BandPartition

theorem ThreeSum.BandPartition.index_bounds {n g i : ℕ} (hg : 0 < g) (hi : i < n) :
    start g (i/g) ≤ i ∧ i < stop n g (i/g) := by sorry
