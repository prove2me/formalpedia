-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyEnumeration_globalKeys_bounded
-- name    : ThreeSum.GlobalKeyEnumeration.globalKeys_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:50.932638+00:00
-- url     : https://prove2.me/theorems/d2464e2e-2e43-4798-b816-b18371411a9f
-- title:
--   Global Key Enumeration: global Keys bounded
-- statement:
--   The Global Key Enumeration construction uses the global Keys bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L149-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L149-L152

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

theorem ThreeSum.GlobalKeyEnumeration.globalKeys_bounded (h J : ℕ) :
    ∀ x ∈ globalKeys h J,
      |x| ≤ (((512*h*localPrime h)*(localPrime h+1)^J : ℕ) : ℤ) := by sorry
