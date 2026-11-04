-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteAEquiv_label
-- name    : ThreeSum.BandRawA.finiteAEquiv_label
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:32.29079+00:00
-- url     : https://prove2.me/theorems/337a8851-2a54-4fa8-adfe-dcc0ccda63c8
-- title:
--   Band Raw A: finite AEquiv label
-- statement:
--   The Band Raw A construction uses the finite AEquiv label property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L80-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L80-L84

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.finiteAEquiv_label (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length)
    (j : Fin (row n g s (rs.getD s default)).length) :
    labelAt n g rs (finiteAEquiv n g rs s hs j).val.val=
      ⟨s,BandPartition.start g (rs.getD s default).a+j.val⟩ := by sorry
