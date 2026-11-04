-- Prove2me | Theorems.Thm_ThreeSum_BandEnumeration_owners_nodup
-- name    : ThreeSum.BandEnumeration.owners_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:03.486771+00:00
-- url     : https://prove2.me/theorems/ed828520-6f09-4338-8cf4-507b6b4c4446
-- title:
--   Band Enumeration: owners nodup
-- statement:
--   The Band Enumeration construction uses the owners nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L139-L157
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L139-L157

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family

theorem ThreeSum.BandEnumeration.owners_nodup (A B C : Family) : (owners A B C).Nodup := by sorry
