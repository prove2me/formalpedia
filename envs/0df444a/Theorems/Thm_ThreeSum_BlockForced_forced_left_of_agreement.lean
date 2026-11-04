-- Prove2me | Theorems.Thm_ThreeSum_BlockForced_forced_left_of_agreement
-- name    : ThreeSum.BlockForced.forced_left_of_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:14.324122+00:00
-- url     : https://prove2.me/theorems/f2f0c7ca-0eb2-44ce-bced-3aee7c0ffd67
-- title:
--   Block Forced: forced left of agreement
-- statement:
--   The Block Forced construction uses the forced left of agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L103-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L103-L112

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
set_option autoImplicit false
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding
variable {J L : ℕ}

theorem ThreeSum.BlockForced.forced_left_of_agreement (I : Finset (Fin J)) (u v : Fin J → Finset (Fin L))
    (hv : ∀ i ∈ I, v i = u i) :
    prefixLeft I u ∪ join Iᶜ v = flat v := by sorry
