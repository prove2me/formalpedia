-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_finiteAIndices
-- name    : ThreeSum.BandRawA.mem_finiteAIndices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:45.725749+00:00
-- url     : https://prove2.me/theorems/2c3f56a8-baee-4561-87dc-fb618bac2a25
-- title:
--   Band Raw A: mem finite AIndices
-- statement:
--   The Band Raw A construction uses the mem finite AIndices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L44-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L44-L47

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.mem_finiteAIndices {n g s : ℕ} {rs : List Record}
    {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ i.val ∈ aIndices n g rs s := by sorry
