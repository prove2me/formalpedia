-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceBuild_flat_bound
-- name    : ThreeSum.LightBlockSourceBuild.flat_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:52.947698+00:00
-- url     : https://prove2.me/theorems/b1005c74-cfbb-401f-b327-7c0e4b541e46
-- title:
--   Light Block Source Build: flat bound
-- statement:
--   The Light Block Source Build construction uses the flat bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L22-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L22-L27

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000

theorem ThreeSum.LightBlockSourceBuild.flat_bound {h J : ℕ} (o : Occurrences h J) (b : Bool) {i : ℕ}
    (hi : i < J*(512*h)) :
    flat J (512*h) (localPrime h) (occurrenceIndices o) (mapRow h b) i ≤
      localPrime h^J*localPrime h := by sorry
