-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawA_time_bound
-- name    : ThreeSum.LightBandRawA.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:22.273011+00:00
-- url     : https://prove2.me/theorems/139ec7e7-aa71-4d2b-98a5-8726d0d53d98
-- title:
--   Light Band Raw A: time bound
-- statement:
--   The Light Band Raw A construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawA.lean#L207-L209
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawA.lean#L207-L209

import Definitions.Def_Submission_ThreeSum_LightBandRawAStep
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_LightBandRawA
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawA
open Light BandCandidateRows BandRawA
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {records src n g vals : ℕ} {rs : List Record} {f : ℕ → ℤ}

theorem ThreeSum.LightBandRawA.time_bound (N g : ℕ) : time N g ≤ 1000*(N+1)*(g+1) := by sorry
