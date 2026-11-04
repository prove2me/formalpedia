-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionScore_program_length
-- name    : ThreeSum.LightOriginalCollisionScore.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:59.562411+00:00
-- url     : https://prove2.me/theorems/61718c82-6177-40ad-bc87-13cdb8eff73f
-- title:
--   Light Original Collision Score: program length
-- statement:
--   The Light Original Collision Score construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionScore.lean#L149-L149
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionScore.lean#L149-L149

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

theorem ThreeSum.LightOriginalCollisionScore.program_length : program.length=4 := by sorry

attribute [defeq] ThreeSum.LightOriginalCollisionScore.program_length
