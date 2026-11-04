-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMetadata_writeRecord_kept
-- name    : ThreeSum.LightTernaryMetadata.writeRecord_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:58.141206+00:00
-- url     : https://prove2.me/theorems/16e28005-1479-4d81-84a7-bf779cba57b3
-- title:
--   Light Ternary Metadata: write Record kept
-- statement:
--   The Light Ternary Metadata construction uses the write Record kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMetadata.lean#L63-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMetadata.lean#L63-L70

import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryMetadata.writeRecord_kept {μ : ℕ → ℤ} {base n j : ℕ} {q z0 z1 m : ℤ}
    (hj : j < n) : SameOutside μ (writeRecord μ base n j q z0 z1 m) base (4*n) := by sorry
