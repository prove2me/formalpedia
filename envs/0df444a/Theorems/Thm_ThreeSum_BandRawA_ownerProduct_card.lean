-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_ownerProduct_card
-- name    : ThreeSum.BandRawA.ownerProduct_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:48.350566+00:00
-- url     : https://prove2.me/theorems/69049bae-1dd6-4faf-a6c8-e6cfabd8f741
-- title:
--   Band Raw A: owner Product card
-- statement:
--   The Band Raw A construction uses the owner Product card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L80-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L80-L84

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.ownerProduct_card (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) :
    (ownerProduct nA nB nC g rs s).card=
      (row nA g s (rs.getD s default)).length*
        bandLength nB g (rs.getD s default).b*bandLength nC g (rs.getD s default).c := by sorry
