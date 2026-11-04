-- Prove2me | Theorems.Thm_ThreeSum_LightBandEnumeration_Tables_sound_ac
-- name    : ThreeSum.LightBandEnumeration.Tables.sound_ac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:03.941108+00:00
-- url     : https://prove2.me/theorems/0a10c51d-01f7-483e-8c0b-0eeabb65481f
-- title:
--   Tables: sound ac
-- statement:
--   The Tables construction uses the sound ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L322-L331
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L322-L331

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

theorem ThreeSum.LightBandEnumeration.Tables.sound_ac {μ : ℕ → ℤ} {dst i j k : ℕ} {A B C : Family}
    (ht : Tables μ dst A B C) (hi : i < A.size) (hk : k < C.size)
    (hr : μ (dst+B.size*C.size+A.size*B.size+i*C.size+k) = (j+1 : ℕ)) :
    j < B.size ∧ Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (i,j,k) := by sorry
