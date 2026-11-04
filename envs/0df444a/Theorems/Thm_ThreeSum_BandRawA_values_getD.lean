-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_values_getD
-- name    : ThreeSum.BandRawA.values_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:18.430201+00:00
-- url     : https://prove2.me/theorems/4a62744e-0b97-48f2-89c5-e515aac71604
-- title:
--   Band Raw A: values get D
-- statement:
--   The Band Raw A construction uses the values get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L123-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L123-L127

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.values_getD {n g k : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hk : k < (items n g rs).length) :
    (values f (items n g rs)).getD k 0=f (labelAt n g rs k).position := by sorry
