-- Prove2me | Theorems.Thm_ThreeSum_BandEnumeration_total_lookupComparisons_le
-- name    : ThreeSum.BandEnumeration.total_lookupComparisons_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:50.712633+00:00
-- url     : https://prove2.me/theorems/fa28b79c-c65c-4934-b5aa-2830b04940ca
-- title:
--   Band Enumeration: total lookup Comparisons le
-- statement:
--   The actual lookups over the enumerated owners take O(m² log m)
--   comparisons.  Constant-size candidate tests add only O(m²) operations.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L203-L217
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L203-L217

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family

theorem ThreeSum.BandEnumeration.total_lookupComparisons_le (A B C : Family) :
    ((owners A B C).map (lookupComparisons A B C)).sum ≤
      (B.size * C.size + A.size * (B.size + C.size)) *
        (Nat.log 2 A.size + Nat.log 2 B.size + Nat.log 2 C.size + 1) := by sorry
