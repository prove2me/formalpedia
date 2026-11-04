-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteAllProducts_card
-- name    : ThreeSum.BandRawA.finiteAllProducts_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:54.301799+00:00
-- url     : https://prove2.me/theorems/24d32ba1-7d62-441b-b9bb-6f4abf85a38a
-- title:
--   Band Raw A: finite All Products card
-- statement:
--   The Band Raw A construction uses the finite All Products card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L105-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L105-L107

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.finiteAllProducts_card (nA nB nC g : ℕ) (rs : List Record) :
    (finiteAllProducts nA nB nC g rs).card=(allProducts nA nB nC g rs).card := by sorry
