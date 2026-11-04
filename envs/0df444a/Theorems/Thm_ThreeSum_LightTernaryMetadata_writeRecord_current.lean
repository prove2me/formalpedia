-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMetadata_writeRecord_current
-- name    : ThreeSum.LightTernaryMetadata.writeRecord_current
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:42.86867+00:00
-- url     : https://prove2.me/theorems/20eae81a-fc80-4548-85c5-16dfb1bea598
-- title:
--   Light Ternary Metadata: write Record current
-- statement:
--   The Light Ternary Metadata construction uses the write Record current property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMetadata.lean#L41-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMetadata.lean#L41-L52

import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryMetadata.writeRecord_current {μ : ℕ → ℤ} {base n j W low high m : ℕ} (hj : j < n) :
    RecordAt (writeRecord μ base n j (LightTernaryCodes.digit W low high m)
      (LightTernaryCodes.zeroCode W low high m) (LightTernaryCodes.oneCode W high m) m)
      base n j W low high m := by sorry
