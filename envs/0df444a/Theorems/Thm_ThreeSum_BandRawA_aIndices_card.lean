-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_aIndices_card
-- name    : ThreeSum.BandRawA.aIndices_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:35.734912+00:00
-- url     : https://prove2.me/theorems/f091211a-1e11-49f2-8180-a53b43b9f68e
-- title:
--   Band Raw A: a Indices card
-- statement:
--   The Band Raw A construction uses the a Indices card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L70-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L70-L73

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.aIndices_card (n g : ℕ) (rs : List Record) (s : ℕ) :
    (aIndices n g rs s).card=(row n g s (rs.getD s default)).length := by sorry
