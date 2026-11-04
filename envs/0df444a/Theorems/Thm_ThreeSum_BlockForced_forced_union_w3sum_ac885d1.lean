-- Prove2me | Theorems.Thm_ThreeSum_BlockForced_forced_union_w3sum_ac885d1
-- name    : ThreeSum.BlockForced.forced_union_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:10.736202+00:00
-- url     : https://prove2.me/theorems/5fe5efeb-0a4f-4bf0-beba-bfea5776d0aa
-- title:
--   Block Forced: forced union
-- statement:
--   The Block Forced construction uses the forced union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L39-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L39-L68

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

theorem ThreeSum.BlockForced.forced_union_w3sum_ac885d1 (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (hu : ∀ i ∈ I, u i ⊆ Q i) (x : Finset (Coord J L)) (hx : x ⊆ remaining I Q) :
    (prefixLeft I u ∪ x) ∪ (prefixRight I Q u ∪ (remaining I Q \ x)) = flat Q := by sorry
