-- Prove2me | Theorems.Thm_ThreeSum_LightBandEnumeration_At_keep
-- name    : ThreeSum.LightBandEnumeration.At.keep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:36:10.031361+00:00
-- url     : https://prove2.me/theorems/8cbf3649-8f68-42a9-b4e4-3e923a0eac9a
-- title:
--   At: keep
-- statement:
--   The At construction uses the keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L31-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L31-L40

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandEnumeration.At.keep {μ μ' : ℕ → ℤ} {lo hi bound : ℕ} {A : Family}
    (h : At μ lo hi A) (hk : Kept μ μ' bound)
    (hlo : lo+A.size ≤ bound) (hhi : hi+A.size ≤ bound) : At μ' lo hi A := by sorry
