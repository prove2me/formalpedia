-- Prove2me | Theorems.Thm_ThreeSum_LightBandEnumeration_Tables_sound_ab
-- name    : ThreeSum.LightBandEnumeration.Tables.sound_ab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:03.054565+00:00
-- url     : https://prove2.me/theorems/1da2c48c-d8a5-4559-8975-d2f0b45dceed
-- title:
--   Tables: sound ab
-- statement:
--   The Tables construction uses the sound ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L311-L320
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L311-L320

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

theorem ThreeSum.LightBandEnumeration.Tables.sound_ab {μ : ℕ → ℤ} {dst i j k : ℕ} {A B C : Family}
    (ht : Tables μ dst A B C) (hi : i < A.size) (hj : j < B.size)
    (hr : μ (dst+B.size*C.size+i*B.size+j) = (k+1 : ℕ)) :
    k < C.size ∧ Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (i,j,k) := by sorry
