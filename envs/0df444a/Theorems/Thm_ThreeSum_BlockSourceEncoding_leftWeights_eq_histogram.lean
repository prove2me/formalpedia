-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceEncoding_leftWeights_eq_histogram
-- name    : ThreeSum.BlockSourceEncoding.leftWeights_eq_histogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:29:27.107202+00:00
-- url     : https://prove2.me/theorems/be625620-b732-4840-b606-fb4a465d976d
-- title:
--   Block Source Encoding: left Weights eq histogram
-- statement:
--   The Block Source Encoding construction uses the left Weights eq histogram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceEncoding.lean#L63-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceEncoding.lean#L63-L74

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceEncoding
open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {β : Type*} [DecidableEq β]

theorem ThreeSum.BlockSourceEncoding.leftWeights_eq_histogram {h J n : ℕ} (o : Occurrences h J) (p : ℕ)
    (B : Finset β) (b : β → ℤ) (S : Finset (BlockRows.Coord J (512*h)))
    (values : ℕ → ℤ) (e : Fin n ≃ B)
    (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    leftWeights o (p : ℤ) B b S =
      if LeftAllowed o S then
        LightHistogram.count (fun i => key p (modulus h J) 0 (values i))
          (LightResidues.residue (modulus h J) 1 (endpointLeft o S)) n
      else 0 := by sorry
