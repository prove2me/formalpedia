-- Prove2me | Theorems.Thm_ThreeSum_BandEnumeration_mem_owners
-- name    : ThreeSum.BandEnumeration.mem_owners
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:03.516031+00:00
-- url     : https://prove2.me/theorems/236f1ed4-884d-43c3-b5d0-19e95bb9d178
-- title:
--   Band Enumeration: mem owners
-- statement:
--   The Band Enumeration construction uses the mem owners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L132-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L132-L133

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family

theorem ThreeSum.BandEnumeration.mem_owners (A B C : Family) (o : Owner A B C) : o ∈ owners A B C := by sorry
