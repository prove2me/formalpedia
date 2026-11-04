-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceRows_hash_eq_eval
-- name    : ThreeSum.BlockSourceRows.hash_eq_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:55.010013+00:00
-- url     : https://prove2.me/theorems/e4bc660f-9525-421b-b49c-872808c84273
-- title:
--   Block Source Rows: hash eq eval
-- statement:
--   The Block Source Rows construction uses the hash eq eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceRows.lean#L39-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceRows.lean#L39-L49

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_BlockSourceRows
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceRows
open Finset BlockRows BlockIndex LightSourceRowScan
open LocalHashMoments
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem ThreeSum.BlockSourceRows.hash_eq_eval {L : ℕ} (s : Finset (Fin L)) (b : ℕ → ℕ)
    (w0 w1 : Fin L → ℕ) (hb : ∀ i : Fin L, b i.val = if i ∈ s then 1 else 0) :
    hash b (OneHotMask.extend w0) (OneHotMask.extend w1) L =
      OneHotMask.eval (OneHotMask.extend w0) (OneHotMask.extend w1)
        L (SubsetAddress.subsetMask s) := by sorry
