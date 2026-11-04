-- Prove2me | Theorems.Thm_ThreeSum_SourceBandData_At_transfer_w3sum_ac885d1
-- name    : ThreeSum.SourceBandData.At.transfer_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:32:26.250097+00:00
-- url     : https://prove2.me/theorems/c5c286dc-3cb3-43d4-8bbe-3f323bc1fd53
-- title:
--   At: transfer
-- statement:
--   The At construction uses the transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L22-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L22-L47

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_SourceBandData
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout

theorem ThreeSum.SourceBandData.At.transfer_w3sum_ac885d1 {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (hm : 0 < m)
    (hhead : ∀ q < 6, ν (base+6*i+q)=μ (base+6*i+q))
    (hdata : ∀ x, hist base n g m i ≤ x → x < flat base n g m i+cap n g → ν x=μ x) :
    At ν f base n g p m shift i := by sorry
