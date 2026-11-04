-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionScore_time_eq
-- name    : ThreeSum.LightOriginalCollisionScore.time_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:19.259219+00:00
-- url     : https://prove2.me/theorems/f4068f9d-4926-4b74-acc9-ab5098d991b8
-- title:
--   Light Original Collision Score: time eq
-- statement:
--   The Light Original Collision Score construction uses the time eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionScore.lean#L144-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionScore.lean#L144-L146

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalCollisionScore
open Light Finset
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightOriginalCollisionScore.time_eq (n q : ℕ) : time n q=74*n+13*q+217 := by sorry
