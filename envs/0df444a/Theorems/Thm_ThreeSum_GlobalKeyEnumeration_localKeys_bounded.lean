-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyEnumeration_localKeys_bounded
-- name    : ThreeSum.GlobalKeyEnumeration.localKeys_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:58.978869+00:00
-- url     : https://prove2.me/theorems/d9d0c9f3-b4a9-42bb-96ff-f58e274fe61b
-- title:
--   Global Key Enumeration: local Keys bounded
-- statement:
--   The Global Key Enumeration construction uses the local Keys bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L143-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L143-L147

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem ThreeSum.GlobalKeyEnumeration.localKeys_bounded (h : ℕ) :
    ∀ x ∈ localKeys h, |x| ≤ ((512*h*localPrime h : ℕ) : ℤ) := by sorry
