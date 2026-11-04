-- Prove2me | Theorems.Thm_ThreeSum_LightSortedBands_Prepared_transfer_w3sum_ac885d1
-- name    : ThreeSum.LightSortedBands.Prepared.transfer_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:28.801648+00:00
-- url     : https://prove2.me/theorems/2bab0d14-7b02-4a9d-80d9-207b47a5c322
-- title:
--   Prepared: transfer
-- statement:
--   Later stages may alter other memory, provided the value and endpoint
--   regions of this class are retained.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean#L182-L203
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean#L182-L203

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_LightSortedBands
set_option autoImplicit false
open ThreeSum ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSortedBands.Prepared.transfer_w3sum_ac885d1 {μ μ' : ℕ → ℤ} {values endpoints g : ℕ} {original : List ℤ}
    (h : Prepared μ values endpoints g original)
    (hk : ∀ a, (values ≤ a ∧ a < values+original.length) ∨
      (endpoints ≤ a ∧ a < endpoints+2+2*original.length) → μ' a = μ a) :
    Prepared μ' values endpoints g original := by sorry
