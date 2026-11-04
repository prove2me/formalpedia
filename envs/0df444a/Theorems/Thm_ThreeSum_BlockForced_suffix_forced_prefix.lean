-- Prove2me | Theorems.Thm_ThreeSum_BlockForced_suffix_forced_prefix
-- name    : ThreeSum.BlockForced.suffix_forced_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:14.818842+00:00
-- url     : https://prove2.me/theorems/137d8f20-c06e-4b20-835a-12364150cd76
-- title:
--   Block Forced: suffix forced prefix
-- statement:
--   The Block Forced construction uses the suffix forced prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L93-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L93-L101

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

theorem ThreeSum.BlockForced.suffix_forced_prefix (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (x : Finset (Coord J L)) (hx : x ⊆ remaining I Q) :
    join Iᶜ (row (prefixLeft I u ∪ x)) = x := by sorry
