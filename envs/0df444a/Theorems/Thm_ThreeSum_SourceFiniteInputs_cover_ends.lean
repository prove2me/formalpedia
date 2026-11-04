-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteInputs_cover_ends
-- name    : ThreeSum.SourceFiniteInputs.cover_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:18:20.257787+00:00
-- url     : https://prove2.me/theorems/3a0030ed-880b-417c-b780-ac4d417d37df
-- title:
--   Source Finite Inputs: cover ends
-- statement:
--   The Source Finite Inputs construction uses the cover ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteInputs.lean#L20-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteInputs.lean#L20-L30

import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteInputs
open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule

theorem ThreeSum.SourceFiniteInputs.cover_ends (free h J : ℕ) :
    maps free h+2*(512*h)*scheduleSize h ≤ LightCoverKeyData.keyEnd free h J ∧
    candidates free h+scheduleSize h ≤ LightCoverKeyData.keyEnd free h J ∧
    leftCounts free h+rows h*localPrime h ≤ LightCoverKeyData.keyEnd free h J ∧
    rightCounts free h+rows h*localPrime h ≤ LightCoverKeyData.keyEnd free h J := by sorry
