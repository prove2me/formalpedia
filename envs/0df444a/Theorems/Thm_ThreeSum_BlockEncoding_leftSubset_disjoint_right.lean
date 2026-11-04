-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_disjoint_right
-- name    : ThreeSum.BlockEncoding.leftSubset_disjoint_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:49.962873+00:00
-- url     : https://prove2.me/theorems/5ffec3dc-2e22-4e80-83d2-367594d134d4
-- title:
--   Block Encoding: left Subset disjoint right
-- statement:
--   The Block Encoding construction uses the left Subset disjoint right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L53-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L53-L58

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.leftSubset_disjoint_right {h J : ℕ} (t : ChoiceTuple h J) :
    Disjoint (leftSubset t) (rightSubset t) := by sorry
