-- Prove2me | Theorems.Thm_ThreeSum_LightBlockCoefficients_map_end_le
-- name    : ThreeSum.LightBlockCoefficients.map_end_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:10.750233+00:00
-- url     : https://prove2.me/theorems/65520542-02e9-4508-861e-b5a6986d41c1
-- title:
--   Light Block Coefficients: map end le
-- statement:
--   The Light Block Coefficients construction uses the map end le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockCoefficients.lean#L61-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockCoefficients.lean#L61-L64

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

theorem ThreeSum.LightBlockCoefficients.map_end_le {M L s : ℕ} (hs : s < M) : 2*L*s+L+L ≤ 2*L*M := by sorry
