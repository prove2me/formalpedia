-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceBuild_endpointLeft_abs_le
-- name    : ThreeSum.LightBlockSourceBuild.endpointLeft_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:53:19.619323+00:00
-- url     : https://prove2.me/theorems/8769f3a3-b232-4685-9b0a-122dfb3fe7ae
-- title:
--   Light Block Source Build: endpoint Left abs le
-- statement:
--   The Light Block Source Build construction uses the endpoint Left abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L29-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L29-L34

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000

theorem ThreeSum.LightBlockSourceBuild.endpointLeft_abs_le {h J : ℕ} (o : Occurrences h J)
    (S : Finset (BlockRows.Coord J (512*h))) :
    |endpointLeft o S| ≤ (endpointBound h J : ℤ) := by sorry
