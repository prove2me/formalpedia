-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_at_injective
-- name    : ThreeSum.BandRawA.at_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:01.780566+00:00
-- url     : https://prove2.me/theorems/67c80754-f91b-49c8-8b2d-b410c95a6906
-- title:
--   Band Raw A: at injective
-- statement:
--   The Band Raw A construction uses the at injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L114-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L114-L121

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.at_injective {n g : ℕ} {rs : List Record} {i j : ℕ}
    (hi : i < (items n g rs).length) (hj : j < (items n g rs).length)
    (he : labelAt n g rs i=labelAt n g rs j) : i=j := by sorry
