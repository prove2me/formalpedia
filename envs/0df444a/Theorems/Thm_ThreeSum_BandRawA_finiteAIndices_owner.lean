-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteAIndices_owner
-- name    : ThreeSum.BandRawA.finiteAIndices_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:17.082902+00:00
-- url     : https://prove2.me/theorems/b87d414a-547e-46ef-a300-c9720be11f96
-- title:
--   Band Raw A: finite AIndices owner
-- statement:
--   The Band Raw A construction uses the finite AIndices owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L66-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L66-L70

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.finiteAIndices_owner {n g s : ℕ} {rs : List Record}
    (hs : s < rs.length) {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ (labelAt n g rs i.val).owner=s := by sorry
