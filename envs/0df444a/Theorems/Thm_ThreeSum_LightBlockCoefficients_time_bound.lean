-- Prove2me | Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
-- name    : ThreeSum.LightBlockCoefficients.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:03.95463+00:00
-- url     : https://prove2.me/theorems/227a9093-ca85-4499-bedd-1aff8387fc29
-- title:
--   Light Block Coefficients: time bound
-- statement:
--   The Light Block Coefficients construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockCoefficients.lean#L231-L233
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockCoefficients.lean#L231-L233

import Definitions.Def_Submission_ThreeSum_LightScaleArray
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockCoefficients
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBlockCoefficients.time_bound (J L : ℕ) : time J L ≤ 300*(J+1)*(L+1) := by sorry
