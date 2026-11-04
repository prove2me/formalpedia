-- Prove2me | Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
-- name    : ThreeSum.LightMaskUnion.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:33:22.702286+00:00
-- url     : https://prove2.me/theorems/d031d58f-cb61-487b-b076-c3ef4b0639d6
-- title:
--   Light Mask Union: time bound
-- statement:
--   The Light Mask Union construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskUnion.lean#L177-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskUnion.lean#L177-L179

import Definitions.Def_Submission_ThreeSum_MaskUnion
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskUnion
set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskUnion
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open MaskUnion
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightMaskUnion.time_bound (W : ℕ) : time W ≤ 800*(W+1)^2 := by sorry
