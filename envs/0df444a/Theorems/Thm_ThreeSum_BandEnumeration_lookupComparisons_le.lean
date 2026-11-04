-- Prove2me | Theorems.Thm_ThreeSum_BandEnumeration_lookupComparisons_le
-- name    : ThreeSum.BandEnumeration.lookupComparisons_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:05.814479+00:00
-- url     : https://prove2.me/theorems/4cc2e008-ccd3-4dcb-b632-888a0889059f
-- title:
--   Band Enumeration: lookup Comparisons le
-- statement:
--   The Band Enumeration construction uses the lookup Comparisons le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L193-L199
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L193-L199

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family

theorem ThreeSum.BandEnumeration.lookupComparisons_le (A B C : Family) (o : Owner A B C) :
    lookupComparisons A B C o ≤
      Nat.log 2 A.size + Nat.log 2 B.size + Nat.log 2 C.size + 1 := by sorry
