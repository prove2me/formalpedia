-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceEncoding_rightWeights_eq_histogram
-- name    : ThreeSum.BlockSourceEncoding.rightWeights_eq_histogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:21.518323+00:00
-- url     : https://prove2.me/theorems/53fd0514-1bec-4f2c-a93a-1e6d69ce3a2c
-- title:
--   Block Source Encoding: right Weights eq histogram
-- statement:
--   The Block Source Encoding construction uses the right Weights eq histogram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceEncoding.lean#L76-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceEncoding.lean#L76-L87

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceEncoding
open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {β : Type*} [DecidableEq β]

theorem ThreeSum.BlockSourceEncoding.rightWeights_eq_histogram {h J n : ℕ} (o : Occurrences h J) (p : ℕ) (shift : ℤ)
    (C : Finset β) (c : β → ℤ) (S : Finset (BlockRows.Coord J (512*h)))
    (values : ℕ → ℤ) (e : Fin n ≃ C)
    (hvalues : ∀ i : Fin n, values i.val = c (e i)) :
    rightWeights o (p : ℤ) shift C c S =
      if RightAllowed o S then
        LightHistogram.count (fun i => key p (modulus h J) shift (values i))
          (LightResidues.residue (modulus h J) 1 (endpointRight o S)) n
      else 0 := by sorry
