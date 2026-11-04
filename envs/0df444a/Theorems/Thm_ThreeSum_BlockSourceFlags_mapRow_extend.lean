-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceFlags_mapRow_extend
-- name    : ThreeSum.BlockSourceFlags.mapRow_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:05:08.775173+00:00
-- url     : https://prove2.me/theorems/c831dd8c-306a-4ea6-96f9-643b25ba73ae
-- title:
--   Block Source Flags: map Row extend
-- statement:
--   The Block Source Flags construction uses the map Row extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L38-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L38-L40

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000

theorem ThreeSum.BlockSourceFlags.mapRow_extend {h : ℕ} (s : Occurrence h) (b : Bool) :
    mapRow h b s.val = OneHotMask.extend (fun i => (mapAt h s (i,b)).val) := by sorry
