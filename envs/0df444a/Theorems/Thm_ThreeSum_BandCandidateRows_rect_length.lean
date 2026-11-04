-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_rect_length
-- name    : ThreeSum.BandCandidateRows.rect_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:13.816002+00:00
-- url     : https://prove2.me/theorems/254bda64-3914-49b9-895f-a2b61ab6fbf9
-- title:
--   Band Candidate Rows: rect length
-- statement:
--   The Band Candidate Rows construction uses the rect length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L69-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandCandidateRows.lean#L69-L70

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

theorem ThreeSum.BandCandidateRows.rect_length (m n : ℕ) (F : ℕ → ℕ → Record) : (rect m n F).length=m*n := by sorry
