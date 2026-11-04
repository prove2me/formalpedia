-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorSourcesCosts_time_eq
-- name    : ThreeSum.EncodedColorSourcesCosts.time_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:13:20.655657+00:00
-- url     : https://prove2.me/theorems/0fca53dc-9506-47e2-b190-b2e9d367e148
-- title:
--   Encoded Color Sources Costs: time eq
-- statement:
--   The Encoded Color Sources Costs construction uses the time eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorSourcesCosts.lean#L20-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorSourcesCosts.lean#L20-L23

import Definitions.Def_Submission_ThreeSum_LightEncodedColorSources
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorSourcesCosts
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorSourcesCosts
open Scales TrimScales BandScales

theorem ThreeSum.EncodedColorSourcesCosts.time_eq (n p U M : ℕ) :
    time n p U M=SourceFiniteCosts.time n p U M+20*blockCount (inputBits n)+1020 := by sorry
