-- Prove2me | Theorems.Thm_ThreeSum_LightBandEnumeration_Tables_covers
-- name    : ThreeSum.LightBandEnumeration.Tables.covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:45:25.732342+00:00
-- url     : https://prove2.me/theorems/f3421cfd-82da-4445-ba20-4b52659e5e0f
-- title:
--   Tables: covers
-- statement:
--   The actual emitted owner tables cover every relevant triple.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L334-L348
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L334-L348

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandEnumeration.Tables.covers {μ : ℕ → ℤ} {dst : ℕ} {A B C : Family}
    (ht : Tables μ dst A B C) (i : A.Index) (j : B.Index) (k : C.Index)
    (hr : relevant A B C (i,j,k)) :
    μ (dst+j.val*C.size+k.val) = (i.val+1 : ℕ) ∨
      μ (dst+B.size*C.size+i.val*B.size+j.val) = (k.val+1 : ℕ) ∨
      μ (dst+B.size*C.size+A.size*B.size+i.val*C.size+k.val) = (j.val+1 : ℕ) := by sorry
