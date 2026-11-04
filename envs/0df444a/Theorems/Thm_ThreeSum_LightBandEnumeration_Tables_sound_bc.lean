-- Prove2me | Theorems.Thm_ThreeSum_LightBandEnumeration_Tables_sound_bc
-- name    : ThreeSum.LightBandEnumeration.Tables.sound_bc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:10.293681+00:00
-- url     : https://prove2.me/theorems/55fafd1a-dd65-4a0c-adfe-2043ddef78bd
-- title:
--   Tables: sound bc
-- statement:
--   The Tables construction uses the sound bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L300-L309
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L300-L309

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

theorem ThreeSum.LightBandEnumeration.Tables.sound_bc {μ : ℕ → ℤ} {dst i j k : ℕ} {A B C : Family}
    (ht : Tables μ dst A B C) (hj : j < B.size) (hk : k < C.size)
    (hr : μ (dst+j*C.size+k) = (i+1 : ℕ)) :
    i < A.size ∧ Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (i,j,k) := by sorry
