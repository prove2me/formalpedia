-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceRows_bits_fin
-- name    : ThreeSum.BlockSourceRows.bits_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:41.547132+00:00
-- url     : https://prove2.me/theorems/8b9ace3b-e0b2-45d6-af5f-ed19d19f77fb
-- title:
--   Block Source Rows: bits fin
-- statement:
--   The Block Source Rows construction uses the bits fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceRows.lean#L23-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceRows.lean#L23-L26

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_BlockSourceRows
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceRows
open Finset BlockRows BlockIndex LightSourceRowScan
open LocalHashMoments
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem ThreeSum.BlockSourceRows.bits_fin {J L : ℕ} (S : Finset (Coord J L)) (j : Fin J) (i : Fin L) :
    bits S j i.val = if i ∈ row S j then 1 else 0 := by sorry
