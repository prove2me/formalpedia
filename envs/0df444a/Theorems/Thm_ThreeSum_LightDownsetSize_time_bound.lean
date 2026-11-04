-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
-- name    : ThreeSum.LightDownsetSize.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:36:48.714299+00:00
-- url     : https://prove2.me/theorems/4a192d37-25e4-4f76-8232-82888505b94f
-- title:
--   Light Downset Size: time bound
-- statement:
--   The Light Downset Size construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean#L100-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean#L100-L104

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetSize
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetSize.time_bound (L : ℕ) : time L ≤ 1400*(L+1)^2 := by sorry
