-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_finiteBandPositions
-- name    : ThreeSum.BandRawA.mem_finiteBandPositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:29.715194+00:00
-- url     : https://prove2.me/theorems/3484440e-53a4-401e-98f5-ec9aee2bce53
-- title:
--   Band Raw A: mem finite Band Positions
-- statement:
--   The Band Raw A construction uses the mem finite Band Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L49-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L49-L51

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.mem_finiteBandPositions {n g a : ℕ} {i : Fin n} :
    i ∈ finiteBandPositions n g a ↔ i.val ∈ bandPositions n g a := by sorry
