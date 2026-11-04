-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceEncoding_key_eq_iff
-- name    : ThreeSum.BlockSourceEncoding.key_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:52.922206+00:00
-- url     : https://prove2.me/theorems/4e746cd5-a162-43ae-b0ef-dd13031312f1
-- title:
--   Block Source Encoding: key eq iff
-- statement:
--   The Block Source Encoding construction uses the key eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceEncoding.lean#L20-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceEncoding.lean#L20-L24

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceEncoding
open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem ThreeSum.BlockSourceEncoding.key_eq_iff {p m : ℕ} (hm : 0 < m) (shift x endpoint : ℤ) :
    key p m shift x = LightResidues.residue m 1 endpoint ↔
      (m : ℤ) ∣ x % (p : ℤ) + shift - endpoint := by sorry
