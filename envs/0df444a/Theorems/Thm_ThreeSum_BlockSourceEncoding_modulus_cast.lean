-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_cast
-- name    : ThreeSum.BlockSourceEncoding.modulus_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:37:40.336746+00:00
-- url     : https://prove2.me/theorems/4264f9f0-e98e-47c4-aa3f-79a97ca8c991
-- title:
--   Block Source Encoding: modulus cast
-- statement:
--   The Block Source Encoding construction uses the modulus cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceEncoding.lean#L56-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceEncoding.lean#L56-L57

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceEncoding
open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem ThreeSum.BlockSourceEncoding.modulus_cast (h J : ℕ) : (modulus h J : ℤ) = globalModulus h J := by sorry
