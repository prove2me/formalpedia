-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_finiteOwnerProduct
-- name    : ThreeSum.BandRawA.mem_finiteOwnerProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:45:47.070652+00:00
-- url     : https://prove2.me/theorems/4c17afad-11e8-49a7-9a32-22b260726294
-- title:
--   Band Raw A: mem finite Owner Product
-- statement:
--   The Band Raw A construction uses the mem finite Owner Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L53-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L53-L58

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.mem_finiteOwnerProduct {nA nB nC g s : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteOwnerProduct nA nB nC g rs s ↔
      coordinates t ∈ ownerProduct nA nB nC g rs s := by sorry
