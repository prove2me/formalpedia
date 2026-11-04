-- Prove2me | Theorems.Thm_ThreeSum_BlockIndex_maskHash_left_w3sum_ac885d1
-- name    : ThreeSum.BlockIndex.maskHash_left_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:57.311277+00:00
-- url     : https://prove2.me/theorems/328200ac-7d93-427c-967d-13ee2ceb74d4
-- title:
--   Block Index: mask Hash left
-- statement:
--   The Block Index construction uses the mask Hash left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L101-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockIndex.lean#L101-L118

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_Submission_ThreeSum_BlockIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndex
open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

theorem ThreeSum.BlockIndex.maskHash_left_w3sum_ac885d1 {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (maskHash o false S : ℤ) = endpointLeft o S := by sorry
