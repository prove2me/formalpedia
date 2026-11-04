-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_index_lt
-- name    : ThreeSum.BandCandidateRows.index_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:20.017527+00:00
-- url     : https://prove2.me/theorems/ac894d48-e8bd-40d0-92f0-880efdea0a34
-- title:
--   Band Candidate Rows: index lt
-- statement:
--   The Band Candidate Rows construction uses the index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L83-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L83-L86

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

theorem ThreeSum.BandCandidateRows.index_lt {i j m n : ℕ} (hi : i < m) (hj : j < n) : i*n+j < m*n := by sorry
