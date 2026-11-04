-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceEncoding_count_eq_sum_of_equiv
-- name    : ThreeSum.BlockSourceEncoding.count_eq_sum_of_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:27.944381+00:00
-- url     : https://prove2.me/theorems/6890af2f-51a0-4059-aa24-eb13b9e9421e
-- title:
--   Block Source Encoding: count eq sum of equiv
-- statement:
--   The Block Source Encoding construction uses the count eq sum of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceEncoding.lean#L36-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceEncoding.lean#L36-L50

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceEncoding
open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem ThreeSum.BlockSourceEncoding.count_eq_sum_of_equiv {β : Type*} [DecidableEq β]
    {p m n : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (B : Finset β) (b : β → ℤ) (values : ℕ → ℤ)
    (e : Fin n ≃ B) (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    LightHistogram.count (fun i => key p m shift (values i))
      (LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by sorry
