-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_ownerProduct_card_le
-- name    : ThreeSum.BandRawA.ownerProduct_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:29:00.787175+00:00
-- url     : https://prove2.me/theorems/5b942ef2-e01b-4ccd-8f56-795ae5f72341
-- title:
--   Band Raw A: owner Product card le
-- statement:
--   The Band Raw A construction uses the owner Product card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L86-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L86-L92

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.ownerProduct_card_le (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) :
    (ownerProduct nA nB nC g rs s).card ≤ g^3 := by sorry
