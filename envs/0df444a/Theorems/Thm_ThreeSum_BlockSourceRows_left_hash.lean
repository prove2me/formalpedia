-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceRows_left_hash
-- name    : ThreeSum.BlockSourceRows.left_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:00.689423+00:00
-- url     : https://prove2.me/theorems/ecfc970a-99bd-48e6-8b7e-278b2e44ed25
-- title:
--   Block Source Rows: left hash
-- statement:
--   The Block Source Rows construction uses the left hash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceRows.lean#L51-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceRows.lean#L51-L56

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_BlockSourceRows
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceRows
open Finset BlockRows BlockIndex LightSourceRowScan
open LocalHashMoments
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem ThreeSum.BlockSourceRows.left_hash {h J : ℕ} (S : Finset (Coord J (512*h))) (j : Fin J)
    (w : Weight (512*h) (LocalField h)) :
    (hash (bits S j) (OneHotMask.extend fun i => (w (i,false)).val)
      (OneHotMask.extend fun i => (w (i,true)).val) (512*h) : ℤ) =
      GlobalEncoding.rawHash w (LocalGraph.leftWord (row S j)) := by sorry
