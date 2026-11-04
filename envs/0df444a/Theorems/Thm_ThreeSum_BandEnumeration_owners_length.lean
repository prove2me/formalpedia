-- Prove2me | Theorems.Thm_ThreeSum_BandEnumeration_owners_length
-- name    : ThreeSum.BandEnumeration.owners_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:30.030931+00:00
-- url     : https://prove2.me/theorems/dd07ff1d-0758-4ef9-ace7-13ebc7fd3654
-- title:
--   Band Enumeration: owners length
-- statement:
--   The Band Enumeration construction uses the owners length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L135-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L135-L137

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family

theorem ThreeSum.BandEnumeration.owners_length (A B C : Family) :
    (owners A B C).length = B.size * C.size + A.size * (B.size + C.size) := by sorry
