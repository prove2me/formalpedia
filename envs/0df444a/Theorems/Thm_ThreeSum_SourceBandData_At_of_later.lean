-- Prove2me | Theorems.Thm_ThreeSum_SourceBandData_At_of_later
-- name    : ThreeSum.SourceBandData.At.of_later
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:32:55.969521+00:00
-- url     : https://prove2.me/theorems/9be3025f-70dc-4fa4-a622-d31dde28ea3c
-- title:
--   At: of later
-- statement:
--   The At construction uses the of later property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L49-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L49-L62

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_SourceBandData
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout

theorem ThreeSum.SourceBandData.At.of_later {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i k : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i)
    (K : KeptBut μ ν (hist base n g m k) (base+6*k) 6)
    (hm : 0 < m) (hik : i < k) (hk : k < size n g) :
    At ν f base n g p m shift i := by sorry
