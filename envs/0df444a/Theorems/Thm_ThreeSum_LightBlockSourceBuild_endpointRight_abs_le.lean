-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceBuild_endpointRight_abs_le
-- name    : ThreeSum.LightBlockSourceBuild.endpointRight_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:17.512176+00:00
-- url     : https://prove2.me/theorems/0a1644d9-5a71-4367-aa93-956ad6cb4814
-- title:
--   Light Block Source Build: endpoint Right abs le
-- statement:
--   The Light Block Source Build construction uses the endpoint Right abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L36-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L36-L41

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000

theorem ThreeSum.LightBlockSourceBuild.endpointRight_abs_le {h J : ℕ} (o : Occurrences h J)
    (S : Finset (BlockRows.Coord J (512*h))) :
    |endpointRight o S| ≤ (endpointBound h J : ℤ) := by sorry
